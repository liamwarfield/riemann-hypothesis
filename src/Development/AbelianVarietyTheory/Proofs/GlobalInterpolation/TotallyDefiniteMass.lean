module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryMassLatticeEqGenusMass
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NormalisedPullbackCommutesSymmetricTranslations
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalVectorsSameLengthOneUnitaryOrbit
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DualLatticeDifferentIndex
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinprodLocalDifferentIdealNormEqDiscr
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HasProdQuadExtLocalEulerFactorInvInv
public import Formalism.LocalToGlobal.GlobalTheory.GL3.LinkThetaStatementFamily

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TotallyDefiniteMass
noncomputable section

namespace GlobalTheory.Proof.TotallyDefiniteMass

open NumberField IsDedekindDomain Formalism.UG Formalism.UG.CS Formalism.BasicNotions Formalism.L2.Herm
open scoped TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke

theorem mass_tMap {K V V' : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V']
    [IsScalarTower (𝓞 K) K V'] {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
    (e : V ≃ₗ[K] V') (he : ∀ x y, h' (e x) (e y) = h x y) (L : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.mass h L = Formalism.HermitianLatticesTheory.mass h' (Formalism.MainNotions.StandardLattice.tMap e L) := by
  by_cases hex : ∃ s', Formalism.ThetaLiftIndependence.IsClassReps h' (Formalism.MainNotions.StandardLattice.tMap e L) s'
  · refine Formalism.MainNotions.StandardLattice.mass_transport e he L hex fun s hs => ?_
    rw [Formalism.HermitianLatticesTheory.massBasic_mass_eq h' _ hex]
    apply Complex.ofReal_injective
    rw [Formalism.HermitianLatticesTheory.massBasic_sum_cast, Formalism.HermitianLatticesTheory.massBasic_sum_cast]
    exact Formalism.ThetaLiftIndependence.latLiftIndep K V' h' _ _ _ (fun _ _ _ => rfl) (fun _ _ _ => rfl) _ _ hex.choose_spec hs
  · have hex' : ¬ ∃ s, Formalism.ThetaLiftIndependence.IsClassReps h L s := fun ⟨s, hs⟩ => hex ⟨_, Formalism.MainNotions.StandardLattice.tMap_reps e he L s hs⟩
    unfold Formalism.HermitianLatticesTheory.mass
    rw [dite_eq_right hex, dite_eq_right hex']

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem isTotDef_gram (hc : CMData F E) (S : HSpace E) (h1 : S.SigOK) (h2 : S.IsPosDef) :
    IsTotDef hc.sig S.gram := by
  obtain ⟨hσ, hJ⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND F E hc
  refine ⟨hc.totReal, fun ι => ?_⟩
  letI : Algebra F ℂ := ((algebraMap ℝ ℂ).comp ι).toAlgebra
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let τ : E →ₐ[F] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine (Formalism.UG.Final.DefSig F E _ hc.sig S.gram ι (τ : E →+* ℂ) (RingHom.ext (hσ.2.2.2 (τ : E →+* ℂ)))
    (RingHom.ext fun a => τ.commutes a) (fun e he => (hc.fixed e).1 he)
    (Matrix.ext fun i j => (hJ S).1 i j) (hJ S).2.isUnit).2 (Or.inl ?_)
  have := h1 (τ : E →+* ℂ)
  rw [h2] at this
  simpa using this

private theorem span_eq_top_of_unimodular (S : HSpace E) (N : Submodule (𝓞 E) S.V)
    (hN : N.FG) (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT N) :
    Submodule.span E (N : Set S.V) = ⊤ := by
  classical
  by_contra hspan
  obtain ⟨φ, hφ₀, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hspan)
  obtain ⟨bs, hbs⟩ := Formalism.HermitianLatticesTheory.dualLattice_dualBasis S.hT S.nondeg S.frame
  let μ := ∑ j, star (φ (S.frame j)) • bs j
  have hμ : ∀ v, S.hT μ v = φ v := by
    have key : S.hT μ = φ := by
      apply S.frame.ext
      intro i
      dsimp only [μ]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, LinearMap.sum_apply]
      have hs : ∀ j, S.hT (star (φ (S.frame j)) • bs j) (S.frame i) =
          φ (S.frame j) * (if i = j then 1 else 0) := by
        intro j
        rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
        congr 1
        rw [← S.herm.eq (S.frame i) (bs j), hbs]
        split_ifs <;> simp
      simp only [hs, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    intro v
    rw [key]
  have hμ₀ : μ ≠ 0 := by
    intro h
    apply hφ₀
    ext y
    simpa [h] using (hμ y).symm
  have hline (a : E) : a • μ ∈ N := by
    rw [← hU]
    change a • μ ∈ Formalism.E.hdual S.hT N
    simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
    intro y hy
    have hy₀ := LinearMap.mem_ker.mp (hφ (Submodule.subset_span hy))
    simp [← S.herm.eq (a • μ) y, LinearMap.map_smulₛₗ, hμ, hy₀]
  obtain ⟨ψ, hψ, -⟩ := Submodule.exists_le_ker_of_notMem
    (show μ ∉ (⊥ : Submodule E S.V) by simpa using hμ₀)
  let f := ψ.restrictScalars (𝓞 E)
  have hmap (x : E) : x ∈ N.map f := by
    refine ⟨(x / ψ μ) • μ, hline _, ?_⟩
    change ψ ((x / ψ μ) • μ) = x
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hψ]
  obtain ⟨d, hd₀, hd⟩ := FractionalIdeal.isFractional_of_fg
    (S := nonZeroDivisors (𝓞 E)) (hN.map f)
  have hinj := IsFractionRing.injective (𝓞 E) E
  have hne {a : 𝓞 E} (ha : a ≠ 0) : algebraMap (𝓞 E) E a ≠ 0 :=
    fun h => ha (hinj (h.trans (map_zero _).symm))
  have hinteger (x : E) : IsLocalization.IsInteger (𝓞 E) x := by
    have hx := hd _ (hmap ((algebraMap (𝓞 E) E d)⁻¹ * x))
    rwa [Algebra.smul_def, ← mul_assoc, mul_inv_cancel₀ (hne (nonZeroDivisors.ne_zero hd₀)),
      one_mul] at hx
  apply RingOfIntegers.not_isField E
  refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, ?_⟩
  intro a ha
  obtain ⟨b, hb⟩ := hinteger ((algebraMap (𝓞 E) E a)⁻¹)
  refine ⟨b, hinj ?_⟩
  rw [map_mul, hb, map_one, mul_inv_cancel₀ (hne ha)]

theorem cosetSum (hc : CMData F E) (S : HSpace E) (h1 : S.SigOK) (h2 : S.IsPosDef)
    (N : Submodule (𝓞 E) S.V) (hN : Submodule.IsLattice E N)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT N) :
    CosetGroupMembership.CosetSum (UFin hc S) (CosetGroupMembership.stabHat hc S N) (Formalism.HermitianLatticesTheory.mass S.hT N) := by
  obtain ⟨hσ, hJ⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND F E hc
  have hd := isTotDef_gram hc S h1 h2
  have hτ : ∀ τ : E →+* ℂ, τ.comp (hc.sig : E →+* E) = (starRingEnd ℂ).comp τ :=
    fun τ => RingHom.ext (hσ.2.2.2 τ)
  have hH : IsHerm (hc.sig : E →+* E) S.gram := Matrix.ext fun i j => (hJ S).1 i j
  have hL : Submodule.IsLattice E (crdLat S N) := Formalism.MainNotions.StandardLattice.tMap_lattice (crd S) N hN
  have hspan : Submodule.span E (crdLat S N : Set (Fin S.rank → E)) = ⊤ := by
    rw [← LinearEquiv.range (crd S), ← Submodule.map_top, ← span_eq_top_of_unimodular S N hN.fg hU,
      Submodule.map_span]
    congr 1
  have hf : Module.Finite (𝓞 E) (crdLat S N) := Module.Finite.iff_fg.2 hL.fg
  have hs : ∀ e, (hc.sig : E →+* E) ((hc.sig : E →+* E) e) = e := fun e => star_star e
  have hm := GlobalTheory.Mass.classMass_lattice_eq_genus_mass hσ (hJ S) hd hs (crdLat S N) hf hspan
  have ht : Formalism.HermitianLatticesTheory.mass S.hT N =
      Formalism.HermitianLatticesTheory.mass (formJ (hc.sig : E →+* E) hs S.gram 1 :
        (Fin S.rank → E) →ₗ⋆[E] (Fin S.rank → E) →ₗ[E] E) (crdLat S N) := by
    refine mass_tMap (crd S) (fun x y => ?_) N
    rw [hT_crd hc]
    change Matrix.toLinearMapₛₗ₂' E (starRingEnd E) (RingHom.id E) ((1 : E) • S.gram) (crd S x) (crd S y) = _
    unfold hform
    rw [Matrix.toLinearMapₛₗ₂'_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [one_smul, smul_eq_mul, RingHom.id_apply]
    change star _ * _ = star _ * _ * _
    ring
  rw [CosetGroupMembership.stabHat_eq]
  refine ⟨Formalism.UG.Final.ClassSetFiniteL F E _ hc.sig S.gram hτ hH (hJ S).2.isUnit hd _ hf hspan,
    fun y => (CosetGroupEquiv.cosetGrpEquiv _ _ y).finite_iff.2
      (Formalism.UG.Final.AdelicStabFiniteL F E _ hc.sig S.gram hτ hH (hJ S).2.isUnit hd _ hf hspan y),
    fun ι _ y hy => ?_⟩
  simp only [CosetGroupEquiv.card_cosetGrp]
  exact (GlobalTheory.Mass.classMass_eq_sum_of_bijective y hy).symm.trans (hm.trans ht.symm)

theorem generalForm : CosetGroupMembership.GeneralForm :=
  fun _ _ _ _ _ _ _ _ hc S h1 h2 N hN hU => cosetSum hc S h1 h2 N hN hU

theorem massAsCosetSum : CosetGroupMembership.MassAsCosetSum :=
  ⟨generalForm, CosetGroupEquiv.column_of_general generalForm⟩

end GlobalTheory.Proof.TotallyDefiniteMass

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdmissibleLatticeBasisExists
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsPrincipalIdealRingLoc
namespace GlobalTheory.CoprimeBasisExistence

open NumberField nonZeroDivisors

def coprimeSet (A : Type*) [CommRing A] (m : ℕ) : Submonoid A where
  carrier := {x | ∃ k : ℕ, 0 < k ∧ k.Coprime m ∧ (k : A) = x}
  one_mem' := ⟨1, one_pos, by simp, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, ha', rfl⟩ ⟨b, hb, hb', rfl⟩
    exact ⟨a * b, mul_pos ha hb, Nat.Coprime.mul_left ha' hb', by simp⟩

theorem coprimeSet_le (A : Type*) [CommRing A] [IsDomain A] [CharZero A] (m : ℕ) :
    coprimeSet A m ≤ A⁰ := by
  rintro _ ⟨k, hk, _, rfl⟩
  exact mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.2 hk.ne')

theorem mem_of_natCast_mem {R : Type*} [CommRing R] (m : ℕ)
    (hu : ∀ k : ℕ, 0 < k → k.Coprime m → IsUnit (k : R)) (P : Ideal R) (hP : P.IsPrime) :
    ∀ n : ℕ, 0 < n → (n : R) ∈ P → (m : R) ∈ P := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hnP
    by_cases hc : n.Coprime m
    · exact absurd hnP (fun h => hP.ne_top (Ideal.eq_top_of_isUnit_mem _ h (hu n hn hc)))
    · have hg0 : 0 < Nat.gcd n m := Nat.gcd_pos_of_pos_left m hn
      have hg1 : 1 < Nat.gcd n m := by
        rw [Nat.Coprime] at hc
        omega
      have hn' : n = Nat.gcd n m * (n / Nat.gcd n m) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left n m)).symm
      have hmul : ((Nat.gcd n m : R) * ((n / Nat.gcd n m : ℕ) : R)) ∈ P := by
        rw [← Nat.cast_mul, ← hn']
        exact hnP
      rcases hP.mem_or_mem hmul with h1 | h1
      · obtain ⟨c, hc'⟩ := Nat.gcd_dvd_right n m
        have e : (m : R) = (Nat.gcd n m : R) * (c : R) := by
          rw [← Nat.cast_mul, ← hc']
        rw [e]
        exact P.mul_mem_right _ h1
      · have hlt : n / Nat.gcd n m < n := Nat.div_lt_self hn hg1
        have hpos : 0 < n / Nat.gcd n m := Nat.div_pos (Nat.gcd_le_left m hn) hg0
        exact ih (n / Nat.gcd n m) hlt hpos h1

theorem isPrincipalIdealRing_loc {K : Type} [Field K] [NumberField K] (m : ℕ) (hm : 0 < m)
    (R : Type) [CommRing R] [IsDomain R] [Algebra (𝓞 K) R]
    [IsLocalization (coprimeSet (𝓞 K) m) R] : IsPrincipalIdealRing R := by
  classical
  have hS := coprimeSet_le (𝓞 K) m
  have : IsDedekindDomain R := IsLocalization.isDedekindDomain (𝓞 K) hS R
  have hinj := IsLocalization.injective R hS
  have hm0 : (m : R) ≠ 0 := by
    rw [← map_natCast (algebraMap (𝓞 K) R), map_ne_zero_iff _ hinj]
    exact Nat.cast_ne_zero.mpr hm.ne'
  have hu : ∀ k : ℕ, 0 < k → k.Coprime m → IsUnit (k : R) := by
    intro k hk hc
    have := IsLocalization.map_units R (⟨(k : 𝓞 K), k, hk, hc, rfl⟩ : coprimeSet (𝓞 K) m)
    simpa using this
  refine IsPrincipalIdealRing.of_finite_primes ?_
  have hI : Ideal.span {(m : R)} ≠ 0 := by simpa using hm0
  refine (((Ideal.finite_factors hI).image (fun v => v.asIdeal)).insert ⊥).subset ?_
  intro P hP
  have hP : P.IsPrime := hP
  by_cases h0 : P = ⊥
  · exact Or.inl h0
  · refine Or.inr ⟨⟨P, hP, h0⟩, ?_, rfl⟩
    have h1 : P.under (𝓞 K) ≠ ⊥ := (IsLocalization.bot_lt_under_prime _ R hS P h0).ne'
    have h2 := Ideal.absNorm_mem (P.under (𝓞 K))
    have h3 : Ideal.absNorm (P.under (𝓞 K)) ≠ 0 := by
      rwa [Ne, Ideal.absNorm_eq_zero_iff]
    have h4 : ((Ideal.absNorm (P.under (𝓞 K)) : ℕ) : R) ∈ P := by
      rw [← map_natCast (algebraMap (𝓞 K) R)]
      exact h2
    have := mem_of_natCast_mem m hu P hP _ (Nat.pos_of_ne_zero h3) h4
    simpa [Ideal.dvd_iff_le] using this

theorem exists_basis_coprime {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (m : ℕ) (hm : 0 < m)
    (L : Submodule (𝓞 K) V) (hL : L.FG) :
    ∃ (r : ℕ) (b : Fin r → V), LinearIndependent K b ∧ (∀ i, b i ∈ L) ∧
      ∀ w ∈ L, ∃ k : ℕ, Nat.Coprime k m ∧ k • w ∈ Submodule.span (𝓞 K) (Set.range b) := by
  classical
  have hS := coprimeSet_le (𝓞 K) m
  set R := Localization.subalgebra K (coprimeSet (𝓞 K) m) hS with hR
  have : IsPrincipalIdealRing R := isPrincipalIdealRing_loc (K := K) m hm R
  have hst : IsScalarTower (𝓞 K) R V := ⟨fun a r v => by
    change ((a • (r : K)) • v) = a • ((r : K) • v)
    rw [smul_assoc]⟩

  have key : ∀ (M : Submodule (𝓞 K) V) (v : V), v ∈ Submodule.span R (M : Set V) →
      ∃ k : ℕ, 0 < k ∧ k.Coprime m ∧ k • v ∈ M := by
    intro M v hv
    induction hv using Submodule.span_induction with
    | mem x hx => exact ⟨1, one_pos, by simp, by simpa using hx⟩
    | zero => exact ⟨1, one_pos, by simp, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, ha', hx⟩ := hx
      obtain ⟨b, hb, hb', hy⟩ := hy
      refine ⟨a * b, mul_pos ha hb, Nat.Coprime.mul_left ha' hb', ?_⟩
      rw [smul_add]
      refine M.add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact M.nsmul_mem hx b
      · rw [mul_smul]; exact M.nsmul_mem hy a
    | smul r x _ hx =>
      obtain ⟨a, ha, ha', hx⟩ := hx
      obtain ⟨⟨c, _, b, hb, hb', rfl⟩, hc⟩ := IsLocalization.surj (coprimeSet (𝓞 K) m) r
      refine ⟨a * b, mul_pos ha hb, Nat.Coprime.mul_left ha' hb', ?_⟩
      have h1 : (a * b) • r • x = c • (a • x) := by
        simp only [map_natCast] at hc
        rw [← algebraMap_smul R c, ← hc, mul_smul, smul_comm a, smul_comm a, mul_smul,
          Nat.cast_smul_eq_nsmul, smul_comm b r]
      rw [h1]
      exact M.smul_mem c hx
  let N : Submodule R V := Submodule.span R (L : Set V)
  have hN : N.FG := by
    obtain ⟨s, hs⟩ := hL
    refine ⟨s, ?_⟩
    simp only [N, ← hs]
    exact (Submodule.span_span_of_tower (𝓞 K) R (s : Set V)).symm
  have : Module.Finite R N := Module.Finite.iff_fg.mpr hN
  have : Module.IsTorsionFree R V := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r v h => ?_
    change (r : K) • v = 0 at h
    rcases smul_eq_zero.mp h with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr h
  obtain ⟨r, e⟩ := Module.basisOfFiniteTypeTorsionFree' (R := R) (M := N)
  choose k hk hk' hkL using fun i => key L (e i : V) (e i).2
  refine ⟨r, fun i => k i • (e i : V), ?_, hkL, ?_⟩
  · have h1 : LinearIndependent R (fun i => (e i : V)) :=
      e.linearIndependent.map' N.subtype N.ker_subtype
    have h2 : LinearIndependent K (fun i => (e i : V)) :=
      (LinearIndependent.iff_fractionRing R K).mp h1
    have h3 := h2.units_smul (fun i => Units.mk0 (k i : K) (Nat.cast_ne_zero.mpr (hk i).ne'))
    convert h3 using 1
    funext i
    simp [Units.smul_def, Nat.cast_smul_eq_nsmul]
  · intro w hw
    have hwN : w ∈ N := Submodule.subset_span hw
    have h1 : w ∈ Submodule.span R
        ((Submodule.span (𝓞 K) (Set.range fun i => k i • (e i : V)) : Submodule (𝓞 K) V) : Set V) := by
      have h2 : w = ∑ i, e.repr ⟨w, hwN⟩ i • (e i : V) := by
        have := congrArg Subtype.val (e.sum_repr ⟨w, hwN⟩)
        rw [Submodule.coe_sum] at this
        exact this.symm
      rw [h2]
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
      have hu : IsUnit (k i : R) := by
        have := IsLocalization.map_units R
          (⟨(k i : 𝓞 K), k i, hk i, hk' i, rfl⟩ : coprimeSet (𝓞 K) m)
        simpa using this
      obtain ⟨u, hu⟩ := hu
      have h3 : (e i : V) = ((u⁻¹ : Rˣ) : R) • (k i • (e i : V)) := by
        rw [← Nat.cast_smul_eq_nsmul R, ← hu, ← mul_smul, Units.inv_mul, one_smul]
      rw [h3]
      exact Submodule.smul_mem _ _
        (Submodule.subset_span (Submodule.subset_span ⟨i, rfl⟩))
    obtain ⟨a, -, ha, h⟩ := key _ w h1
    exact ⟨a, ha, h⟩

end GlobalTheory.CoprimeBasisExistence
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdmissibleLatticeBasisExists
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.HomLocBasis

open GlobalTheory.PlaceInt.LocBasis Module

theorem exists_basis_primeTo {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (m : ℕ) (hm : 0 < m) (L : Submodule (𝓞 K) V) (hfg : L.FG) :
    ∃ (r : ℕ) (b : Fin r → V), LinearIndependent K b ∧ (∀ i, b i ∈ L) ∧
      ∀ w ∈ L, ∃ k : ℕ, Nat.Coprime k m ∧ k • w ∈ Submodule.span (𝓞 K) (Set.range b) := by
  first
  | exact @_root_.GlobalTheory.CoprimeBasisExistence.exists_basis_coprime
  | exact _root_.GlobalTheory.CoprimeBasisExistence.exists_basis_coprime
  | (apply _root_.GlobalTheory.CoprimeBasisExistence.exists_basis_coprime <;> assumption)
  | (intros; apply _root_.GlobalTheory.CoprimeBasisExistence.exists_basis_coprime <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CoprimeBasisExistence.exists_basis_coprime <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CoprimeBasisExistence.exists_basis_coprime ..)


open Formalism.MainNotions.TaylorLogMetric in
theorem exists_nnBasis : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (p N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), p.Prime → Nat.Coprime (Ideal.absNorm cc) p → TaylorLogMetric.admitted D N N' L L' → ∃ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), TaylorLogMetric.NNBasis D (TaylorLogMetric.tor0 D cc δ) δ p L L' b := by
  intro D cc δ p N N' L L' hp hcc hA
  have hL : StandardLatticesGL3.SD D L := hA.2.2.1
  have hL' : StandardLatticesGL3.SD D L' := hA.2.2.2
  obtain ⟨s, y, y', hy, hy', hexp⟩ := GlobalTheory.HomDual.exists_dual_family_hom D
    (GlobalTheory.exists_trace_dual_family_halfDifferent D) N N' L L' hL hL'
  let Y : Submodule (𝓞 D.host.K) (Matrix (Fin N') (Fin N) D.host.E) :=
    Submodule.span (𝓞 D.host.K) (Set.range y)
  have hYle : ∀ x ∈ Y, x ∈ YYl D L L' := by
    intro x hx
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx
    exact (YYl D L L').sum_mem fun i _ => GlobalTheory.ThetaConj.smul_mem_YYl D L L' (c i) (hy i)
  have hYge : ∀ x ∈ YYl D L L', x ∈ Y := by
    intro x hx
    have hi : ∀ i, ∃ t : 𝓞 D.host.K, (t : D.host.K) = hYY D x (y' i) := fun i =>
      GlobalTheory.NormSum.TraceInt.hYY_integral D N N' L L' hL hL' x hx (y' i) (hy' i)
    choose t ht using hi
    refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨t, ?_⟩
    conv_rhs => rw [hexp x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← ht]; rfl
  obtain ⟨r, b, hli, hb, hw⟩ := exists_basis_primeTo p hp.pos Y (Submodule.fg_span (Set.finite_range y))
  set n : ℕ := Ideal.absNorm cc with hn
  have hn0 : n ≠ 0 := by
    intro h
    rw [h, Nat.coprime_zero_left] at hcc
    exact hp.one_lt.ne' hcc
  have hnK : (n : D.host.K) ≠ 0 := by exact_mod_cast hn0
  refine ⟨r, fun i => n • b i, ⟨?_, fun i => ?_, fun w hwY => ?_⟩, fun i => ?_⟩
  · have := hli.units_smul fun _ => Units.mk0 _ hnK
    have e : (fun i => n • b i) = (fun _ : Fin r => Units.mk0 _ hnK) • b := by
      funext i
      simp [Units.smul_def, Nat.cast_smul_eq_nsmul]
    rw [e]; exact this
  · refine ⟨1, by simp, ?_⟩
    rw [Nat.cast_one, one_smul]
    exact nsmul_mem (hYle _ (hb i)) n
  · obtain ⟨k, hk, hkw⟩ := hw w (hYge w hwY)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hkw
    refine ⟨n * k, Nat.Coprime.mul_left hcc hk, c, ?_⟩
    rw [Nat.cast_smul_eq_nsmul, mul_smul, ← hc, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_comm]; rfl
  · refine AddSubgroup.subset_closure ⟨δ * n, AddSubgroup.subset_closure ⟨(n : 𝓞 D.host.K), Ideal.absNorm_mem cc, ?_⟩,
      b i, hYle _ (hb i), ?_⟩
    · simp
    · funext τ j k
      change δ * embT D τ ((n • b i) j k) = δ * n * embT D τ (b i j k)
      rw [Matrix.smul_apply, map_nsmul, nsmul_eq_mul, mul_assoc]

end GlobalTheory.HomLocBasis
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdmissibleLatticeBasisExistsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_lattice_basis_exists : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (p N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), p.Prime → Nat.Coprime (Ideal.absNorm cc) p → TaylorLogMetric.admitted D N N' L L' → ∃ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), TaylorLogMetric.NNBasis D (TaylorLogMetric.tor0 D cc δ) δ p L L' b := by
  first | exact @GlobalTheory.HomLocBasis.exists_nnBasis | exact GlobalTheory.HomLocBasis.exists_nnBasis | (intros; apply GlobalTheory.HomLocBasis.exists_nnBasis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ProductLocalDensitiesAdeleCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ProductLocalDensitiesAdeleCharacter
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex

noncomputable section

namespace GlobalTheory.LocalDensityProduct

variable {F : Type} [Field F] [NumberField F]

def colonV (v : HeightOneSpectrum (𝓞 F)) (c : Fv F v) : AddSubgroup (Fv F v) :=
  (intV F v).comap (AddMonoidHom.mulRight c)

theorem mem_colonV {v : HeightOneSpectrum (𝓞 F)} {c t : Fv F v} :
    t ∈ colonV v c ↔ t * c ∈ v.adicCompletionIntegers F := Iff.rfl

theorem mem_intV {v : HeightOneSpectrum (𝓞 F)} {t : Fv F v} :
    t ∈ intV F v ↔ t ∈ v.adicCompletionIntegers F := Iff.rfl

theorem card_quot_span (v : HeightOneSpectrum (𝓞 F)) (c : v.adicCompletionIntegers F)
    (hc : (c : Fv F v) ≠ 0) :
    (Nat.card (v.adicCompletionIntegers F ⧸ Ideal.span {c}) : ℝ) = ‖(c : Fv F v)‖⁻¹ := by
  have hv : Valued.v (c : Fv F v) ≠ 0 := by simpa using hc
  have h1 : Valued.v (c : Fv F v) ≤ 1 := c.2
  have hl : WithZero.log (Valued.v (c : Fv F v)) ≤ 0 := by
    rw [← WithZero.exp_le_exp, WithZero.exp_log hv, WithZero.exp_zero]; exact h1
  obtain ⟨e, he⟩ : ∃ e : ℕ, WithZero.log (Valued.v (c : Fv F v)) = -(e : ℤ) :=
    ⟨(-WithZero.log (Valued.v (c : Fv F v))).toNat, by omega⟩
  have he' : Valued.v (c : Fv F v) = WithZero.exp (-(e : ℤ)) := by
    rw [← he, WithZero.exp_log hv]
  rw [(GlobalTheory.CNorm.isAdicComplete_and_card_quotient_adicCompletionIntegers F v).2 c e he',
    FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv]
  rw [he]
  simp

theorem relIndex_colonV_inv (v : HeightOneSpectrum (𝓞 F)) (c : v.adicCompletionIntegers F)
    (hc : (c : Fv F v) ≠ 0) :
    ((colonV v (c : Fv F v)⁻¹).relIndex (intV F v) : ℝ) = ‖(c : Fv F v)‖⁻¹ := by
  let f : v.adicCompletionIntegers F →+ Fv F v :=
    ((v.adicCompletionIntegers F).subtype : _ →+* _).toAddMonoidHom
  have hr : f.range = intV F v := by
    ext x
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  have hcm : (colonV v (c : Fv F v)⁻¹).comap f = (Ideal.span {c}).toAddSubgroup := by
    ext x
    change (x : Fv F v) * (c : Fv F v)⁻¹ ∈ v.adicCompletionIntegers F ↔ x ∈ Ideal.span {c}
    rw [Ideal.mem_span_singleton']
    constructor
    · intro h
      exact ⟨⟨_, h⟩, Subtype.ext (inv_mul_cancel_right₀ hc _)⟩
    · rintro ⟨a, rfl⟩
      change (a : Fv F v) * c * (c : Fv F v)⁻¹ ∈ _
      rw [mul_inv_cancel_right₀ hc]
      exact a.2
  rw [← hr, ← AddSubgroup.index_comap, hcm, ← card_quot_span v c hc]
  rfl

theorem relIndex_intV_colonV (v : HeightOneSpectrum (𝓞 F)) (c : Fv F v) (hc : c ≠ 0) :
    (intV F v).relIndex (colonV v c) = (colonV v c⁻¹).relIndex (intV F v) := by
  have h1 : intV F v = (colonV v c⁻¹).comap (AddMonoidHom.mulRight c) := by
    ext x
    change _ ↔ x * c * c⁻¹ ∈ v.adicCompletionIntegers F
    rw [mul_inv_cancel_right₀ hc]
    rfl
  have hs : Function.Surjective (AddMonoidHom.mulRight c) := fun y =>
    ⟨y * c⁻¹, inv_mul_cancel_right₀ hc y⟩
  conv_lhs => rw [h1]
  rw [AddSubgroup.relIndex_comap, colonV, colonV, AddSubgroup.map_comap_eq_self_of_surjective hs]

theorem index_colonV (v : HeightOneSpectrum (𝓞 F)) (c : Fv F v) (hc : c ≠ 0) :
    ((intV F v).relIndex (colonV v c) ≠ 0 ∧ (colonV v c).relIndex (intV F v) ≠ 0) ∧
      ((intV F v).relIndex (colonV v c) : ℝ) / ((colonV v c).relIndex (intV F v) : ℝ) = ‖c‖⁻¹ := by
  have hn : ‖c‖ ≠ 0 := norm_ne_zero_iff.2 hc
  rcases (v.adicCompletionIntegers F).mem_or_inv_mem c with h | h
  · have e1 : ((intV F v).relIndex (colonV v c) : ℝ) = ‖c‖⁻¹ := by
      rw [relIndex_intV_colonV v c hc]
      exact relIndex_colonV_inv v ⟨c, h⟩ hc
    have e2 : (colonV v c).relIndex (intV F v) = 1 :=
      AddSubgroup.relIndex_eq_one.2 fun x hx => mem_colonV.2 (mul_mem (mem_intV.1 hx) h)
    refine ⟨⟨fun h0 => ?_, by rw [e2]; exact one_ne_zero⟩, by rw [e1, e2]; simp⟩
    rw [h0, Nat.cast_zero] at e1
    exact inv_ne_zero hn e1.symm
  · have e1 : ((colonV v c).relIndex (intV F v) : ℝ) = ‖c‖ := by
      have := relIndex_colonV_inv v ⟨c⁻¹, h⟩ (inv_ne_zero hc)
      simpa using this
    have e2 : (intV F v).relIndex (colonV v c) = 1 :=
      AddSubgroup.relIndex_eq_one.2 fun x hx => by
        have := mul_mem (mem_colonV.1 hx) h
        rwa [mul_inv_cancel_right₀ hc] at this
    refine ⟨⟨by rw [e2]; exact one_ne_zero, fun h0 => ?_⟩, by rw [e1, e2]; simp⟩
    rw [h0, Nat.cast_zero] at e1
    exact hn e1.symm

theorem exists_generator_differentV (v : HeightOneSpectrum (𝓞 F)) :
    ∃ δ : v.adicCompletionIntegers F, (δ : Fv F v) ≠ 0 ∧ differentV F v = Ideal.span {δ} := by
  obtain ⟨δ, hδ⟩ := (IsPrincipalIdealRing.principal (differentV F v)).principal
  refine ⟨δ, fun h => ?_, hδ⟩
  have h0 : δ = 0 := Subtype.ext h
  rw [h0, Submodule.span_zero_singleton, differentV, Ideal.map_eq_bot_iff_of_injective] at hδ
  · exact differentIdeal_ne_bot hδ
  · intro x y hxy
    have := congrArg (fun z : v.adicCompletionIntegers F => (z : Fv F v)) hxy
    simp only [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply] at this
    exact FaithfulSMul.algebraMap_injective (𝓞 F) F ((algebraMap F (Fv F v)).injective this)

theorem psiV_of_eq {ψ₀ ψ : AddChar (AF F) ℂ} {a : F}
    (h : ∀ x, ψ x = ψ₀ (algebraMap F (AF F) a * x)) (v : HeightOneSpectrum (𝓞 F)) (t : Fv F v) :
    psiV F ψ v t = psiV F ψ₀ v (algebraMap F (Fv F v) a * t) := by
  classical
  rw [psiV, psiV, h]
  congr 1
  refine Prod.ext (mul_zero _) ?_
  change algebraMap F (Af F) a * singleV F v t = singleV F v _
  refine DFunLike.ext _ _ fun w => ?_
  change algebraMap F (Fv F w) a * singleV F v t w = _
  by_cases hw : w = v
  · subst hw
    have e : ∀ y : Fv F w, singleV F w y w = y := fun y =>
      RestrictedProduct.single_eq_same _ w y
    rw [e, e]
  · have e : ∀ y : Fv F v, singleV F v y w = 0 := fun y =>
      RestrictedProduct.single_eq_of_ne _ y hw
    rw [e, e, mul_zero]

theorem dual_scaled {ψ₀ ψ : AddChar (AF F) ℂ} {a : F} (ha : a ≠ 0)
    (h : ∀ x, ψ x = ψ₀ (algebraMap F (AF F) a * x)) (v : HeightOneSpectrum (𝓞 F))
    (h₀ : ∀ t : Fv F v, t ∈ dualV F ψ₀ v ↔
      ∀ d ∈ differentV F v, t * (d : Fv F v) ∈ v.adicCompletionIntegers F) :
    ((intV F v).relIndex (dualV F ψ v) ≠ 0 ∧ (dualV F ψ v).relIndex (intV F v) ≠ 0) ∧
      dualIndex F ψ v = normDifferentV F v * ‖algebraMap F (Fv F v) a‖⁻¹ := by
  obtain ⟨δ, hδ, hD⟩ := exists_generator_differentV v
  have e : dualV F ψ v = colonV v (algebraMap F (Fv F v) a * δ) := by
    ext t
    have e1 : t ∈ dualV F ψ v ↔ algebraMap F (Fv F v) a * t ∈ dualV F ψ₀ v := by
      change (∀ s ∈ _, _) ↔ (∀ s ∈ _, _)
      simp only [psiV_of_eq h, mul_assoc]
    rw [e1, h₀, hD, mem_colonV, ← mul_assoc, mul_comm t]
    constructor
    · intro H
      exact H δ (Ideal.mem_span_singleton_self δ)
    · intro H d hd
      obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 hd
      have := mul_mem H z.2
      change _ * ((z : Fv F v) * δ) ∈ _
      rwa [mul_comm (z : Fv F v), ← mul_assoc]
  have hc : algebraMap F (Fv F v) a * δ ≠ 0 := mul_ne_zero ((map_ne_zero _).2 ha) hδ
  rw [dualIndex, e]
  refine ⟨(index_colonV v _ hc).1, ?_⟩
  rw [(index_colonV v _ hc).2, normDifferentV, hD, card_quot_span v δ hδ, norm_mul, mul_inv,
    mul_comm]

theorem eq_of_isScalingInf {ψ₀ ψ : AddChar (AF F) ℂ} (h₀ : IsStdChar F ψ₀) (hψ : IsCharAF F ψ)
    {a : F} (ha : a ≠ 0) (hs : IsScalingInf F ψ a) (x : AF F) :
    ψ x = ψ₀ (algebraMap F (AF F) a * x) := by
  have hc : IsCharAF F (ψ₀.mulShift (algebraMap F (AF F) a)) := by
    refine ⟨h₀.1.1.comp (continuous_const_mul _), fun y => h₀.1.2.1 _, fun b => ?_, ?_⟩
    · rw [AddChar.mulShift_apply, ← map_mul]; exact h₀.1.2.2.1 _
    · obtain ⟨y, hy⟩ := h₀.1.2.2.2
      refine ⟨algebraMap F (AF F) a⁻¹ * y, ?_⟩
      rwa [AddChar.mulShift_apply, ← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul]
  have hs' : IsScalingInf F (ψ₀.mulShift (algebraMap F (AF F) a)) a :=
    isScalingInf_of_eq F h₀ fun _ => rfl
  rw [GlobalTheory.StdAdelicChar.eq_of_psiInf_eq hψ hc fun y => (hs y).trans (hs' y).symm]
  rfl

theorem finite_norm_ne_one {a : F} (ha : a ≠ 0) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ‖algebraMap F (Fv F v) a‖).Finite :=
  (FinitePlace.hasFiniteMulSupport ha).preimage
    (FinitePlace.equivHeightOneSpectrum (K := F)).symm.injective.injOn

theorem absInf_mul_finprod {a : F} (ha : a ≠ 0) :
    absInf F a * ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖algebraMap F (Fv F v) a‖ = 1 := by
  rw [← prod_abs_eq_one ha, ← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
  rfl

theorem summable_eulerInv (E : Type) [Field E] [Algebra F E] (M : ℕ) (hM : 2 ≤ M) :
    Summable fun v => |eulerInv F E M v - 1| := by
  refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun v => ?_)
    (GlobalTheory.PrimeSquareSum.summable_absNorm_inv_sq F).1
  have h1 : (1 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℕ) := by
    exact_mod_cast (HeightOneSpectrum.one_lt_absNorm v).le
  have h2 : |etaV F E v| = 1 := by
    unfold etaV; split_ifs <;> simp
  rw [eulerInv, sub_sub_cancel_left, abs_neg, abs_mul, abs_pow, h2, one_pow, one_mul, resCard,
    zpow_neg, zpow_natCast, abs_of_nonneg (by positivity)]
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ h1 hM)

theorem density_product : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (σ : E →ₐ[F] E), IsCMExt F E σ → (∀ x : E, star x = σ x) → Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ ψ, IsCharAF F ψ → (∀ v, (intV F v).relIndex (dualV F ψ v) ≠ 0 ∧ (dualV F ψ v).relIndex (intV F v) ≠ 0) ∧ ∀ a : F, a ≠ 0 → IsScalingInf F ψ a → ∀ M : ℕ, 2 ≤ M → Summable (fun v => |localDensity F E ψ M v - 1|) ∧ ∃ P : ℝ, 0 < P ∧ HasProd (localDensity F E ψ M) P ∧ absInf F a ^ ((M : ℝ) - 1 / 2) * P = absDiscr F ^ ((1 : ℝ) / 2 - M) / Formalism.HermitianLatticesTheory.lValEta E M := by
  intro F E _ _ _ _ _ _ σ hCM hst hU ψ hψ
  obtain ⟨ψ₀, h₀, -⟩ := GlobalTheory.T.existsUnique_isStandardAdeleChar_unramifiedCM_base F E σ hCM hst hU
  have hd := GlobalTheory.T.dual_lattice_different_index F E σ hCM hst hU ψ₀ h₀
  obtain ⟨hfin, hprod, -⟩ := GlobalTheory.T.finprod_localDifferentIdealNorm_eq_discr F E σ hCM hst hU
  refine ⟨fun v => ?_, fun a ha hs M hM => ?_⟩
  · obtain ⟨a, ha, h⟩ := GlobalTheory.T.exists_eq_standardAdeleChar_rational_dilate F E σ hCM hst hU ψ₀ h₀ ψ hψ
    exact (dual_scaled ha h v (hd v).1).1
  obtain ⟨hL, hE⟩ := GlobalTheory.T.hasProd_quadExtLocalEulerFactorInv_inv F E σ hCM hst hU M hM
  have hn : ∀ v, dualIndex F ψ v = normDifferentV F v * ‖algebraMap F (Fv F v) a‖⁻¹ := fun v =>
    (dual_scaled ha (eq_of_isScalingInf h₀ hψ ha hs) v (hd v).1).2
  have hfa := finite_norm_ne_one ha
  classical
  let S : Finset (HeightOneSpectrum (𝓞 F)) := hfin.toFinset ∪ hfa.toFinset
  have hS : ∀ v ∉ S, dualIndex F ψ v = 1 := fun v hv => by
    simp only [S, Finset.mem_union, Set.Finite.mem_toFinset, Function.mem_mulSupport, not_or,
      not_not] at hv
    rw [hn, hv.1, hv.2]; simp
  have hA : 0 < absInf F a :=
    Finset.prod_pos fun w _ => pow_pos (InfinitePlace.pos_iff.2 ha) _
  have hD : 0 < absDiscr F := abs_pos.2 (by exact_mod_cast discr_ne_zero F)
  have hSp : ∏ v ∈ S, dualIndex F ψ v = absDiscr F * absInf F a := by
    have e1 := absInf_mul_finprod ha
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) (by
      intro v hv; simp only [S, Finset.coe_union, Set.Finite.coe_toFinset]; exact Or.inr hv)] at e1
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) (by
      intro v hv; simp only [S, Finset.coe_union, Set.Finite.coe_toFinset]; exact Or.inl hv)] at hprod
    simp only [hn]
    rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, ← hprod, Nat.cast_prod,
      inv_eq_of_mul_eq_one_left e1]
  have h1 : HasProd (fun v => dualIndex F ψ v ^ ((1 : ℝ) / 2 - M))
      ((absDiscr F * absInf F a) ^ ((1 : ℝ) / 2 - M)) := by
    rw [← hSp, ← Real.finsetProd_rpow _ _ (fun v _ => by rw [hn]; positivity) _]
    exact hasProd_prod_of_ne_finset_one fun v hv => by rw [hS v hv, Real.one_rpow]
  have h2 : HasProd (eulerInv F E M) (Formalism.HermitianLatticesTheory.lValEta E M)⁻¹ := by
    have := Filter.Tendsto.inv₀ hE hL.ne'
    simp only [Finset.prod_inv_distrib, inv_inv] at this
    exact this
  refine ⟨?_, _, by positivity, h1.mul h2, ?_⟩
  · refine (summable_eulerInv E M hM).congr_cofinite ?_
    filter_upwards [S.eventually_cofinite_notMem] with v hv
    rw [localDensity, hS v hv, Real.one_rpow, one_mul]
  · rw [Real.mul_rpow hD.le hA.le, div_eq_mul_inv _ (Formalism.HermitianLatticesTheory.lValEta E M), ← mul_assoc,
      mul_left_comm, ← Real.rpow_add hA]
    simp

end GlobalTheory.LocalDensityProduct

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ProductLocalDensitiesAdeleCharacterStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_localDensities_adeleCharacter : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (σ : E →ₐ[F] E), IsCMExt F E σ → (∀ x : E, star x = σ x) → Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ ψ, IsCharAF F ψ → (∀ v, (intV F v).relIndex (dualV F ψ v) ≠ 0 ∧ (dualV F ψ v).relIndex (intV F v) ≠ 0) ∧ ∀ a : F, a ≠ 0 → IsScalingInf F ψ a → ∀ M : ℕ, 2 ≤ M → Summable (fun v => |localDensity F E ψ M v - 1|) ∧ ∃ P : ℝ, 0 < P ∧ HasProd (localDensity F E ψ M) P ∧ absInf F a ^ ((M : ℝ) - 1 / 2) * P = absDiscr F ^ ((1 : ℝ) / 2 - M) / Formalism.HermitianLatticesTheory.lValEta E M := by
  first | exact @GlobalTheory.LocalDensityProduct.density_product | exact GlobalTheory.LocalDensityProduct.density_product | (intros; apply GlobalTheory.LocalDensityProduct.density_product <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalizedThetaVectorIsometryIsTheta
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalizedThetaVectorIsometryIsTheta
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

namespace GlobalTheory.IsomTheta

theorem isTheta_eNat_comp : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → δ ≠ 0 → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∀ (g : ℕ) (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)), S.d = D.host.d → (∀ x, e x ∈ S.La ↔ x ∈ La D B.tor L L') → (∀ x y, JMB.hf S.Hm (e x) (e y) = Hf D B.tor x y) → S.IsTheta (fun z => B.eNat χ N N' L L' (e.symm z)) := by
  intro D cc δ B χ hcc hδ hχ h0 N N' L L' hA g S e hd hLa hH
  have hS : B.StdOK := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.stdOK B hcc hδ
  have hmem := (B.vec_mem_ne hcc hδ h0 hS χ hχ N N' L L' hA).1
  have hQ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.rational_integrality_link D cc hcc δ hδ B N N' L L' hA
  simp only [Th, ThSp, Set.mem_setOf_eq] at hmem
  refine ⟨?_, ?_⟩
  · have hdiff : Differentiable ℂ (fun z => B.eNat χ N N' L L' (e.symm z)) :=
      hmem.1.comp e.symm.differentiable
    exact ReciprocityTheory.ChartRestriction.G.I2.contDiff_of_differentiable hdiff
  · intro x hx
    have hx0 : e.symm x ∈ La D B.tor L L' := by
      rw [← hLa]; simpa using hx
    obtain ⟨m, hm⟩ := hQ _ hx0
    funext z
    have key := hmem.2 (e.symm x) hx0 (e.symm z)
    have h1 : JMB.hf S.Hm z x = Hf D B.tor (e.symm z) (e.symm x) := by
      simpa using hH (e.symm z) (e.symm x)
    have h2 : JMB.hf S.Hm x x = Hf D B.tor (e.symm x) (e.symm x) := by
      simpa using hH (e.symm x) (e.symm x)
    have hre : (JMB.beta S.d S.Hm x x).re = (m : ℝ) := by
      rw [JMB.beta, h2, hd, Complex.re_ofReal_mul]; exact hm
    have hal : al D B.tor (e.symm x) = (-1 : ℂ) ^ m := by
      rw [al, hm, round_intCast]
    have hph : Complex.exp ((Real.pi : ℂ) * Complex.I * (((JMB.beta S.d S.Hm x x).re : ℝ) : ℂ)) = (-1 : ℂ) ^ m := by
      rw [hre, show (Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ) = (m : ℂ) * ((Real.pi : ℂ) * Complex.I) by push_cast; ring,
        Complex.exp_int_mul, Complex.exp_pi_mul_I]
    show Complex.exp ((Real.pi : ℂ) * Complex.I * (((JMB.beta S.d S.Hm x x).re : ℝ) : ℂ)) *
        (B.eNat χ N N' L L' (e.symm (z + x)) *
          Complex.exp (-(Real.pi : ℂ) * JMB.hf S.Hm z x - (Real.pi : ℂ) / 2 * JMB.hf S.Hm x x)) =
      B.eNat χ N N' L L' (e.symm z)
    rw [← key, hph, ← hal, h1, h2, map_add (f := _)]
    unfold U
    ring_nf

end GlobalTheory.IsomTheta
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalizedThetaVectorIsometryIsThetaStatement
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalizedThetaVector_isometry_isTheta : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → δ ≠ 0 → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∀ (g : ℕ) (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)), S.d = D.host.d → (∀ x, e x ∈ S.La ↔ x ∈ La D B.tor L L') → (∀ x y, JMB.hf S.Hm (e x) (e y) = Hf D B.tor x y) → S.IsTheta (fun z => B.eNat χ N N' L L' (e.symm z)) := by
  first | exact @GlobalTheory.IsomTheta.isTheta_eNat_comp | exact GlobalTheory.IsomTheta.isTheta_eNat_comp | (intros; apply GlobalTheory.IsomTheta.isTheta_eNat_comp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemIntVIffOfSplitting
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.MainNotions.StandardLattice
open scoped TensorProduct

namespace GlobalTheory.SplitIntegers

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem conj_tmul (hc : CMData F E) {R : Type} [CommRing R] [Algebra F R] (a : E) (y : R) :
    Formalism.UG.sigR hc.sig R (a ⊗ₜ[F] y) = star a ⊗ₜ[F] y := rfl

omit [NumberField F] [NumberField E] [StarRing E] in
theorem algebraMap_tmul {R : Type} [CommRing R] [Algebra F R] (c : F) (y : R) :
    (algebraMap F E c) ⊗ₜ[F] y = (1 : E) ⊗ₜ[F] (algebraMap F R c * y) := by
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Algebra.smul_def]

theorem exists_add_conj (hc : CMData F E) {R : Type} [CommRing R] [Algebra F R] (z : E ⊗[F] R) :
    ∃ p : R, z + Formalism.UG.sigR hc.sig R z = (1 : E) ⊗ₜ[F] p := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul a y =>
    obtain ⟨c, h⟩ := (hc.fixed (a + star a)).1 (by simp [add_comm])
    exact ⟨algebraMap F R c * y, by rw [conj_tmul, ← TensorProduct.add_tmul, ← h, algebraMap_tmul]⟩
  | add x y hx hy =>
    obtain ⟨p, hp⟩ := hx
    obtain ⟨q, hq⟩ := hy
    refine ⟨p + q, ?_⟩
    rw [map_add (f := _), TensorProduct.tmul_add, ← hp, ← hq]; ring

theorem exists_of_conj_eq (hc : CMData F E) {R : Type} [CommRing R] [Algebra F R] {z : E ⊗[F] R}
    (hz : Formalism.UG.sigR hc.sig R z = z) : ∃ p : R, (1 : E) ⊗ₜ[F] p = z := by
  obtain ⟨p, hp⟩ := exists_add_conj hc z
  rw [hz, ← two_smul F z] at hp
  refine ⟨(2⁻¹ : F) • p, ?_⟩
  rw [TensorProduct.tmul_smul, ← hp, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

theorem exists_diag (hc : CMData F E) {K : Type} [Field K] [Algebra F K]
    (φ : E ⊗[F] K ≃+* K × K) (hφ : ∀ x, φ (Formalism.UG.sigR hc.sig K x) = swapR _ (φ x)) :
    ∃ θ : K ≃+* K, ∀ y, φ ((1 : E) ⊗ₜ[F] y) = (θ y, θ y) := by
  let f : K →+* K := ((RingHom.fst K K).comp φ.toRingHom).comp
    (Algebra.TensorProduct.includeRight (R := F) (A := E) (B := K)).toRingHom
  have hf : ∀ y, φ ((1 : E) ⊗ₜ[F] y) = (f y, f y) := fun y => by
    have h := hφ ((1 : E) ⊗ₜ[F] y)
    rw [conj_tmul, star_one] at h
    have h2 := congrArg Prod.snd h
    exact Prod.ext rfl h2
  refine ⟨RingEquiv.ofBijective f ⟨f.injective, fun b => ?_⟩, hf⟩
  obtain ⟨p, hp⟩ := exists_of_conj_eq hc (z := φ.symm (b, b)) (φ.injective (by
    rw [hφ, φ.apply_symm_apply]; rfl))
  refine ⟨p, ?_⟩
  have := hf p
  rw [hp, φ.apply_symm_apply] at this
  exact (congrArg Prod.fst this).symm

theorem mem_of_isIntegral (v : HeightOneSpectrum (𝓞 F)) {x : v.adicCompletion F}
    (hx : IsIntegral ℤ x) : x ∈ v.adicCompletionIntegers F := by
  have hi : IsIntegral (v.adicCompletionIntegers F) x := hx.tower_top
  obtain ⟨b, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  exact b.2

omit [NumberField E] [StarRing E] [Algebra F E] in
theorem map_mem {S : Type} (v : HeightOneSpectrum (𝓞 F)) [FunLike S E (v.adicCompletion F)]
    [RingHomClass S E (v.adicCompletion F)] (g : S) (a : 𝓞 E) :
    g (algebraMap (𝓞 E) E a) ∈ v.adicCompletionIntegers F :=
  mem_of_isIntegral v (a.isIntegral_coe.map_of_comp_eq (RingHom.id ℤ)
    (g : E →+* v.adicCompletion F) (RingHom.ext_int _ _))

end GlobalTheory.SplitIntegers

namespace GlobalTheory

open SplitIntegers

theorem mem_intV_iff_of_splitting : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (v : HeightOneSpectrum (𝓞 F)), (∀ (θ : v.adicCompletion F ≃+* v.adicCompletion F) (x : v.adicCompletion F), θ x ∈ v.adicCompletionIntegers F ↔ x ∈ v.adicCompletionIntegers F) → ∀ (φ : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, φ (Formalism.UG.sigR hc.sig (v.adicCompletion F) x) = swapR _ (φ x)) → ∀ x, x ∈ intV E v ↔ (φ x).1 ∈ v.adicCompletionIntegers F ∧ (φ x).2 ∈ v.adicCompletionIntegers F := by
  intro F E _ _ _ _ _ _ hc v hθ φ hφ
  obtain ⟨θ, hd⟩ := exists_diag hc φ hφ
  have hθ' : ∀ y ∈ v.adicCompletionIntegers F, θ.symm y ∈ v.adicCompletionIntegers F :=
    fun y hy => (hθ θ.symm y).2 hy
  let ι : E →+* v.adicCompletion F × v.adicCompletion F := φ.toRingHom.comp
    (Algebra.TensorProduct.includeLeftRingHom (R := F) (A := E) (B := v.adicCompletion F))
  have hι : ∀ a : 𝓞 E,
      (φ (algebraMap (𝓞 E) E a ⊗ₜ[F] 1)).1 ∈ v.adicCompletionIntegers F ∧
      (φ (algebraMap (𝓞 E) E a ⊗ₜ[F] 1)).2 ∈ v.adicCompletionIntegers F := fun a =>
    ⟨map_mem v ((RingHom.fst _ _).comp ι) a, map_mem v ((RingHom.snd _ _).comp ι) a⟩
  intro x
  constructor
  · intro hx
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨⟨_, a, rfl⟩, rfl⟩ | ⟨y, rfl⟩
      · exact hι a
      · beta_reduce
        rw [hd]
        exact ⟨(hθ θ y).2 y.2, (hθ θ y).2 y.2⟩
    | zero => rw [map_zero]; exact ⟨zero_mem _, zero_mem _⟩
    | one => rw [map_one]; exact ⟨one_mem _, one_mem _⟩
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact ⟨add_mem hx.1 hy.1, add_mem hx.2 hy.2⟩
    | neg x _ hx => rw [map_neg]; exact ⟨neg_mem hx.1, neg_mem hx.2⟩
    | mul x y _ _ hx hy => rw [map_mul]; exact ⟨mul_mem hx.1 hy.1, mul_mem hx.2 hy.2⟩
  · rintro ⟨ha, hb⟩
    obtain ⟨P, hP, hPv⟩ := GlobalTheory.Mass.Genus.exists_over (E := E) v
    obtain ⟨w, t, ht, hwt⟩ := hc.cmUnram.2.2 P hP
    obtain ⟨s, hs⟩ := (hc.fixed (algebraMap (𝓞 E) E ((w - t) * (w - t)))).1 (by
      rw [map_mul, map_sub, ht, star_mul, star_sub, star_star]; ring)
    have hsi : IsIntegral ℤ s := by
      have := ((w - t) * (w - t)).isIntegral_coe
      rw [← hs] at this
      exact (isIntegral_algHom_iff (algebraMap F E).toIntAlgHom (algebraMap F E).injective).1 this
    let s' : 𝓞 F := ⟨s, hsi⟩
    have hs' : algebraMap (𝓞 F) (𝓞 E) s' = (w - t) * (w - t) := RingOfIntegers.ext hs
    have hsv : s' ∉ v.asIdeal := fun h => by
      rw [← hPv, Ideal.mem_comap, hs'] at h
      exact hwt ((hP.isPrime.mem_or_mem h).elim id id)
    obtain ⟨u, hu⟩ := ((SelfDualGenus.isUnit_algebraMap_iff v s').2 hsv).exists_left_inv
    have hu' : (u : v.adicCompletion F) * algebraMap F (v.adicCompletion F) s = 1 :=
      congrArg Subtype.val hu
    obtain ⟨hα, hβ⟩ := hι w
    have e1 := hφ (algebraMap (𝓞 E) E w ⊗ₜ[F] 1)
    rw [conj_tmul, ← ht] at e1
    have e2 := hd (algebraMap F (v.adicCompletion F) s * 1)
    rw [← algebraMap_tmul, hs, mul_one, ← mul_one (1 : v.adicCompletion F), map_mul,
      ← Algebra.TensorProduct.tmul_mul_tmul, map_sub, TensorProduct.sub_tmul, map_mul, map_sub,
      e1] at e2
    generalize hW : φ (algebraMap (𝓞 E) E w ⊗ₜ[F] 1) = W at hα hβ e2
    obtain ⟨α, β⟩ := W
    have e3 : (α - β) * (α - β) = θ (algebraMap F (v.adicCompletion F) s) := congrArg Prod.fst e2
    have e4 : θ u * ((α - β) * (α - β)) = 1 := by rw [e3, ← map_mul, hu', map_one]
    have hθu : θ u ∈ v.adicCompletionIntegers F := (hθ θ u).2 u.2
    set c := ((φ x).1 - (φ x).2) * (θ u * (α - β)) with hcdef
    have hcm : c ∈ v.adicCompletionIntegers F :=
      mul_mem (sub_mem ha hb) (mul_mem hθu (sub_mem hα hβ))
    have hx : x = (1 : E) ⊗ₜ[F] θ.symm ((φ x).1 - c * α) +
        ((1 : E) ⊗ₜ[F] θ.symm c) * (algebraMap (𝓞 E) E w ⊗ₜ[F] 1) := by
      apply φ.injective
      rw [map_add (f := _), map_mul, hd, hd, hW, θ.apply_symm_apply, θ.apply_symm_apply]
      refine Prod.ext ?_ ?_
      · change (φ x).1 = (φ x).1 - c * α + c * α
        ring
      · change (φ x).2 = (φ x).1 - c * α + c * β
        rw [hcdef]
        linear_combination ((φ x).1 - (φ x).2) * e4
    rw [hx]
    refine add_mem (Subring.subset_closure (Or.inr ⟨⟨_, hθ' _ (sub_mem ha (mul_mem hcm hα))⟩, rfl⟩))
      (mul_mem (Subring.subset_closure (Or.inr ⟨⟨_, hθ' _ hcm⟩, rfl⟩))
        (Subring.subset_closure (Or.inl ⟨⟨_, w, rfl⟩, rfl⟩)))

end GlobalTheory
end
