module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PlaceDict
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DvdOfIne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelLeIne

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.RadClMul
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem finSupp {K : Type} [Field K] [NumberField K] {G : Type} [CommGroup G]
    (g : HeightOneSpectrum (𝓞 K) → G) (n : ℤ) (a : Kˣ) :
    Function.HasFiniteMulSupport fun v => g v ^ (ordv v a / n) := by
  refine ((clProd K).2.2.1 a).subset fun v hv => ?_
  intro h
  apply hv
  simp [h]

private theorem mk_radCl {K : Type} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) (n : ℕ) (a : Kˣ) :
    (QuotientGroup.mk (radCl n a) : ClS S) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), (QuotientGroup.mk (primeCl v) : ClS S) ^ (ordv v a / n) := by
  have h := (QuotientGroup.mk' (clSub S)).map_finprod (finSupp primeCl (n : ℤ) a)
  simpa [radCl] using h

private theorem mk_primeCl {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ S) : (QuotientGroup.mk (primeCl v) : ClS S) = 1 :=
  (QuotientGroup.eq_one_iff _).2 (Subgroup.subset_closure ⟨v, hv, rfl⟩)

private theorem ordv_pow' {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (b : Kˣ) (n : ℕ) :
    ordv v (b ^ n) = n * ordv v b := by
  induction n with
  | zero => simp [ordv_one]
  | succ m ih => rw [pow_succ, ordv_mul, ih]; push_cast; ring

theorem UpperTheory.V.Kum.radClMul :
    ∀ (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) (n : ℕ), n ≠ 0 → (∀ a ∈ SelK S n, ∀ b ∈ SelK S n, (QuotientGroup.mk (radCl n (a * b)) : ClS S) = QuotientGroup.mk (radCl n a) * QuotientGroup.mk (radCl n b)) ∧
    (∀ a ∈ SelK S n, (QuotientGroup.mk (radCl n a) : ClS S) ^ n = 1) ∧ (∀ a b : Kˣ, radCl n (a * b ^ n) = radCl n a) := by
  intro K _ _ S n hn
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn
  have h1 : ∀ x : Kˣ, radCl 1 x = 1 := (clProd K).2.2.2
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb
    rw [mk_radCl S n, mk_radCl S n, mk_radCl S n,
      ← finprod_mul_distrib (finSupp (fun v => (QuotientGroup.mk (primeCl v) : ClS S)) (n : ℤ) a)
        (finSupp (fun v => (QuotientGroup.mk (primeCl v) : ClS S)) (n : ℤ) b)]
    apply finprod_congr
    intro v
    by_cases hv : v ∈ S
    · simp [mk_primeCl hv]
    · rw [ordv_mul, Int.add_ediv_of_dvd_right (hb v hv), zpow_add]
  · intro a ha
    have e := mk_radCl S 1 a
    rw [h1 a] at e
    simp only [Nat.cast_one, Int.ediv_one, QuotientGroup.mk_one] at e
    have key : ∀ v : HeightOneSpectrum (𝓞 K),
        ((QuotientGroup.mk (primeCl v) : ClS S) ^ (ordv v a / (n : ℤ))) ^ n =
          (QuotientGroup.mk (primeCl v) : ClS S) ^ ordv v a := by
      intro v
      by_cases hv : v ∈ S
      · simp [mk_primeCl hv]
      · rw [← zpow_natCast, ← zpow_mul, Int.ediv_mul_cancel (ha v hv)]
    rw [mk_radCl S n, finprod_pow (finSupp (fun v => (QuotientGroup.mk (primeCl v) : ClS S)) (n : ℤ) a),
      finprod_congr key]
    exact e.symm
  · intro a b
    have e := h1 b
    simp only [radCl, Nat.cast_one, Int.ediv_one] at e
    have hb1 : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 K) => primeCl v ^ ordv v b := by
      have h := finSupp (primeCl (K := K)) 1 b
      simpa only [Int.ediv_one] using h
    simp only [radCl]
    rw [finprod_congr (fun v => show primeCl v ^ (ordv v (a * b ^ n) / (n : ℤ)) =
        primeCl v ^ (ordv v a / (n : ℤ)) * primeCl v ^ ordv v b by
          rw [ordv_mul, ordv_pow', Int.add_mul_ediv_left _ _ hn', zpow_add]),
      finprod_mul_distrib (finSupp primeCl (n : ℤ) a) hb1, e, mul_one]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ResInfMem
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum
open Pointwise

private theorem UpperTheory.V.Kum.coc_conj_triv {R Γ M : Type} [CommRing R] [Group Γ] [AddCommGroup M] [Module R M]
    (ρ : Representation R Γ M) (f : Γ → M) (hf : ∀ g h, f (g * h) = f g + ρ g (f h)) (g h k : Γ)
    (e : k * g = g * h) (hk : ∀ m, ρ k m = m) : f k = ρ g (f h) := by
  have h1 := hf k g
  rw [e, hf, hk, add_comm] at h1
  exact (add_right_cancel h1).symm

theorem UpperTheory.V.Kum.resInfMem :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (D : LData F Ω l) (e : ℤ), (Sha D e).map (resInf D e) ≤ EqHom l (Uinf F Ω l) (qzG F Ω l e) := by
  intro F Ω _ _ _ _ _ l _ D e
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨p1, p2, p3, p4⟩ := placeDict F Ω
  have hchi : ∀ g : G F Ω, D.chi (toGS Ω _ g) = cycZ F Ω l g := fun g => DFunLike.congr_fun D.hchi g
  have htriv : ∀ g : G F Ω, cycZ F Ω l g = 1 → ∀ m, qzTw D e (toGS Ω _ g) m = m := fun g hg m => by
    rw [qzTw_apply, hchi, hg, one_zpow, Units.val_one, one_smul]
  have hz : ∀ a b, z.1 (a * b) = z.1 a + qzTw D e a (z.1 b) := z.2.2
  have hconj : ∀ g h k : G F Ω, k * g = g * h → cycZ F Ω l k = 1 →
      z.1 (toGS Ω _ k) = qzTw D e (toGS Ω _ g) (z.1 (toGS Ω _ h)) := fun g h k e1 hk =>
    coc_conj_triv _ _ hz _ _ _ (by rw [← map_mul, ← map_mul, e1]) (htriv k hk)
  have h1 : z.1 1 = 0 := by
    have := hz 1 1
    rw [one_mul, map_one] at this
    exact left_eq_add.1 this
  have hdec : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ u : Uinf F Ω l, u.1 ∈ Dec (F := F) A →
      z.1 (toGS Ω _ u.1) = 0 := by
    intro A hA u hu
    obtain ⟨v, hv⟩ := p2 A (p3 A l (Fact.out : l.Prime).ne_zero hA)
    have hvS : v ∈ D.S := by
      have := (p4 A v l hv).1 hA
      rw [← D.hS] at this
      exact this
    obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) (D.hA ⟨v, hvS⟩) hv
    obtain ⟨m, hm⟩ := (res_mk_eq_zero_iff D e ⟨v, hvS⟩ z).1 ((mem_Sha_iff D e _).1 hx ⟨v, hvS⟩)
    have hc : g⁻¹ * u.1 * g ∈ Dec (F := F) (D.A ⟨v, hvS⟩) := by
      have h : u.1 • g • D.A ⟨v, hvS⟩ = g • D.A ⟨v, hvS⟩ := hu
      show (g⁻¹ * u.1 * g) • D.A ⟨v, hvS⟩ = D.A ⟨v, hvS⟩
      rw [mul_smul, mul_smul, h, inv_smul_smul]
    have hu1 : cycZ F Ω l u.1 = 1 := u.2.2
    have h2 := hm ⟨_, hc⟩
    rw [htriv _ (by simp [hu1]), sub_self] at h2
    rw [hconj g (g⁻¹ * u.1 * g) u.1 (by group) hu1, h2, map_zero]
  refine ⟨⟨?_, fun a b => ?_, fun A u hu => ?_, hdec⟩, (Submodule.mem_iInf _).2 fun g u u' h => ?_⟩
  · exact (IsLocallyConstant.iff_continuous _).2
      (z.2.1.comp ((continuous_toGS Ω _).comp continuous_subtype_val))
  · rw [resInf_mk, resInf_mk, resInf_mk, Subgroup.coe_mul, map_mul, hz, htriv _ a.2.2]
  · rw [resInf_mk]
    by_cases hA : A = ⊤
    · subst hA
      rw [p1, Subgroup.mem_bot] at hu
      rw [hu, map_one, h1]
    obtain ⟨v, hv⟩ := p2 A hA
    by_cases hl : A.valuation (l : Ω) < 1
    · exact hdec A hl u (Ine_le_Dec A hu)
    have hvS : v ∉ (D.S : Set (HeightOneSpectrum (𝓞 F))) := by
      rw [D.hS]
      exact fun h => hl ((p4 A v l hv).2 h)
    have hn : u.1 ∈ NS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) := by
      apply Subgroup.le_topologicalClosure
      apply Subgroup.subset_normalClosure
      simp only [Set.mem_iUnion]
      exact ⟨v, hvS, A, hv, hu⟩
    have : toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) u.1 = 1 := (QuotientGroup.eq_one_iff _).2 hn
    rw [this, h1]
  · rw [resInf_mk, resInf_mk, hconj g u.1 u'.1 (AlgEquiv.ext h) u'.2.2, qzTw_apply, hchi]
    rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ResInfInj
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem totient_le_finrank_mul_natDegree_minpoly (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [CharZero Ω] (ζ : Ω) (N : ℕ) (hζ : IsPrimitiveRoot ζ N) (hN : 0 < N) : N.totient ≤ Module.finrank ℚ F * (minpoly F ζ).natDegree := by
  have hint : IsIntegral F ζ := (hζ.isIntegral hN).tower_top
  haveI : FiniteDimensional F (IntermediateField.adjoin F ({ζ} : Set Ω)) := IntermediateField.adjoin.finiteDimensional hint
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin F ({ζ} : Set Ω)) := Module.Finite.trans F (IntermediateField.adjoin F ({ζ} : Set Ω))
  rw [← IntermediateField.adjoin.finrank hint, Module.finrank_mul_finrank ℚ F (IntermediateField.adjoin F ({ζ} : Set Ω))]
  have h1 : minpoly ℚ ζ = minpoly ℚ ((⟨ζ, IntermediateField.mem_adjoin_simple_self F ζ⟩ : IntermediateField.adjoin F ({ζ} : Set Ω))) :=
    minpoly.algebraMap_eq (A := ℚ) (algebraMap (IntermediateField.adjoin F ({ζ} : Set Ω)) Ω).injective ⟨ζ, IntermediateField.mem_adjoin_simple_self F ζ⟩
  calc N.totient = (minpoly ℚ ζ).natDegree := by
        rw [← Polynomial.cyclotomic_eq_minpoly_rat hζ hN, Polynomial.natDegree_cyclotomic]
    _ = (minpoly ℚ ((⟨ζ, IntermediateField.mem_adjoin_simple_self F ζ⟩ : IntermediateField.adjoin F ({ζ} : Set Ω)))).natDegree := by rw [h1]
    _ ≤ _ := minpoly.natDegree_le _

private theorem natDegree_minpoly_le_of_cycZ_pow_eq_one (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [CharZero Ω] (l : ℕ) [Fact l.Prime] (k : ℕ) (hk : 0 < k) (h : ∀ g : G F Ω, cycZ F Ω l g ^ k = 1) (n : ℕ) (ζ : Ω) (hζ : IsPrimitiveRoot ζ (l ^ n)) : (minpoly F ζ).natDegree ≤ k := by
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : Normal F Ω := IsAlgClosure.normal F Ω
  haveI : NeZero (l : Ω) := ⟨by exact_mod_cast (Fact.out : l.Prime).ne_zero⟩
  have hint : IsIntegral F ζ := (hζ.isIntegral (pow_pos (Fact.out : l.Prime).pos n)).tower_top
  have hsep : ((minpoly F ζ).map (algebraMap F Ω)).Separable :=
    (minpoly.irreducible hint).separable.map
  have hne : (minpoly F ζ).map (algebraMap F Ω) ≠ 0 :=
    Polynomial.map_ne_zero (minpoly.ne_zero hint)
  let S : Finset ℤ_[l] := (Polynomial.nthRoots k (1 : ℤ_[l])).toFinset
  let T : Finset Ω := S.image (fun x => ζ ^ (PadicInt.toZModPow n x).val)
  have hsub : ((minpoly F ζ).map (algebraMap F Ω)).roots.toFinset ⊆ T := by
    intro y hy
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hne] at hy
    have hy' : Polynomial.aeval y (minpoly F ζ) = 0 := by
      rw [← Polynomial.eval_map_algebraMap]
      exact hy
    have hmy : minpoly F ζ = minpoly F y :=
      minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) hy' (minpoly.monic hint)
    obtain ⟨g, rfl⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := F) (E := Ω)).mp hmy.symm
    rw [Finset.mem_image]
    refine ⟨(cycZ F Ω l g : ℤ_[l]), ?_, ?_⟩
    · rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots hk, ← Units.val_pow_eq_pow_val, h g, Units.val_one]
    · exact (cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (G F Ω) Ω g) ζ hζ.pow_eq_one).symm
  calc (minpoly F ζ).natDegree = ((minpoly F ζ).map (algebraMap F Ω)).natDegree :=
        (Polynomial.natDegree_map _).symm
    _ = Multiset.card ((minpoly F ζ).map (algebraMap F Ω)).roots :=
        IsAlgClosed.card_roots_eq_natDegree.symm
    _ = ((minpoly F ζ).map (algebraMap F Ω)).roots.toFinset.card :=
        (Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hsep)).symm
    _ ≤ T.card := Finset.card_le_card hsub
    _ ≤ S.card := Finset.card_image_le
    _ ≤ Multiset.card (Polynomial.nthRoots k (1 : ℤ_[l])) := Multiset.toFinset_card_le _
    _ ≤ k := Polynomial.card_nthRoots k 1

theorem UpperTheory.V.Kum.resInfInj :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (D : LData F Ω l) (e : ℤ), e ≠ 0 → Procyc F Ω l → Function.Injective (resInf D e) := by
  intro F Ω _ _ _ _ _ l _ D e he hP
  have hcomp : ∀ h : G F Ω, D.chi (QuotientGroup.mk h) = cycZ F Ω l h := by
    intro h
    rw [← D.hchi]
    rfl
  have hchi : Continuous D.chi := by
    apply (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
    have h := continuous_cycZ F Ω l
    convert h using 1
    funext h
    exact hcomp h
  have hINF : ∃ g : G F Ω, cycZ F Ω l g ^ e ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
    have hk : 0 < e.natAbs := Int.natAbs_pos.mpr he
    have hall : ∀ g : G F Ω, cycZ F Ω l g ^ e.natAbs = 1 := by
      intro g
      have h0 := hcon g
      rcases Int.natAbs_eq e with h' | h'
      · rw [h', zpow_natCast] at h0
        exact h0
      · rw [h', zpow_neg, inv_eq_one, zpow_natCast] at h0
        exact h0
    haveI : NeZero (l : Ω) := ⟨by exact_mod_cast (Fact.out : l.Prime).ne_zero⟩
    haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ (e.natAbs * Module.finrank ℚ F + 1))
    have hlb := totient_le_finrank_mul_natDegree_minpoly F Ω ζ _ hζ (pow_pos (Fact.out : l.Prime).pos _)
    have hub := natDegree_minpoly_le_of_cycZ_pow_eq_one F Ω l e.natAbs hk hall _ ζ hζ
    have htot : e.natAbs * Module.finrank ℚ F + 1 ≤ (l ^ (e.natAbs * Module.finrank ℚ F + 1)).totient := by
      rw [Nat.totient_prime_pow_succ (Fact.out : l.Prime)]
      have h1 : e.natAbs * Module.finrank ℚ F < l ^ (e.natAbs * Module.finrank ℚ F) :=
        Nat.lt_pow_self (Fact.out : l.Prime).one_lt
      have h2 : 1 ≤ l - 1 := by
        have := (Fact.out : l.Prime).two_le
        omega
      calc e.natAbs * Module.finrank ℚ F + 1 ≤ l ^ (e.natAbs * Module.finrank ℚ F) := h1
        _ = l ^ (e.natAbs * Module.finrank ℚ F) * 1 := (mul_one _).symm
        _ ≤ _ := Nat.mul_le_mul_left _ h2
    have h3 : Module.finrank ℚ F * (minpoly F ζ).natDegree ≤ Module.finrank ℚ F * e.natAbs :=
      Nat.mul_le_mul_left _ hub
    rw [mul_comm (Module.finrank ℚ F) e.natAbs] at h3
    omega
  have hDIV : ∀ a : ℤ_[l], a ≠ 0 → Function.Surjective (fun m : QZ l => a • m) := by
    intro a ha m
    obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective (ZlSub l) m
    have ha' : algebraMap ℤ_[l] ℚ_[l] a ≠ 0 := by
      intro h0
      apply ha
      exact (FaithfulSMul.algebraMap_injective ℤ_[l] ℚ_[l]) (by rw [h0, map_zero])
    refine ⟨Submodule.Quotient.mk ((algebraMap ℤ_[l] ℚ_[l] a)⁻¹ * q), ?_⟩
    show a • (Submodule.Quotient.mk _ : ℚ_[l] ⧸ ZlSub l) = _
    rw [← Submodule.Quotient.mk_smul, ← algebraMap_smul ℚ_[l] a, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ ha', one_mul]
  rw [← LinearMap.ker_eq_bot]
  unfold resInf resTriv
  apply Submodule.ker_liftQ_eq_bot
  intro z hz
  rw [LinearMap.mem_ker] at hz
  have hclosed : IsClosed ((D.chi.range : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) := by
    rw [MonoidHom.coe_range]
    exact (isCompact_range hchi).isClosed
  have hcond : l ≠ 2 ∨ D.chi.range ≤ KStar.TotallyRealRoots.princ l 2 := by
    rcases hP with h | h
    · exact Or.inl h
    · right
      rintro _ ⟨g, rfl⟩
      obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
      rw [KStar.TotallyRealRoots.princ, MonoidHom.mem_ker, hcomp]
      exact h g'
  obtain ⟨u, huV, hu⟩ := existsGen l D.chi.range hclosed hcond
  obtain ⟨γ, rfl⟩ := huV
  have hcont : ReciprocityTheory.Gal.ContAction (qzTw D e) := by
    apply contScal
    exact Units.continuous_val.comp (hchi.zpow (-e))
  have hne : (((D.chi γ) ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) - 1 ≠ 0 := by
    intro h0
    have h1 : D.chi γ ^ (-e) = 1 := Units.ext (sub_eq_zero.mp h0)
    have h2 : D.chi γ ^ e = 1 := by
      rw [zpow_neg, inv_eq_one] at h1
      exact h1
    obtain ⟨g, hg⟩ := hINF
    apply hg
    have hmem : D.chi (QuotientGroup.mk g) ∈ (Subgroup.zpowers (D.chi γ)).topologicalClosure :=
      hu ⟨_, rfl⟩
    rw [← hcomp]
    have hsub : ((Subgroup.zpowers (D.chi γ)).topologicalClosure : Set ℤ_[l]ˣ) ⊆ {x | x ^ e = 1} := by
      rw [Subgroup.topologicalClosure_coe]
      apply closure_minimal
      · rintro _ ⟨k, rfl⟩
        show ((D.chi γ) ^ k) ^ e = 1
        rw [← zpow_mul, mul_comm, zpow_mul, h2, one_zpow]
      · exact isClosed_eq (continuous_zpow e) continuous_const
    exact hsub hmem
  apply cobOfGen l _ D.chi ℤ_[l] (QZ l) (qzTw D e) γ hchi hcont
  · intro g hg m
    simp [qzTw, scalRep, hg]
  · intro g
    exact hu ⟨g, rfl⟩
  · intro m
    obtain ⟨m', hm'⟩ := hDIV _ hne m
    refine ⟨m', ?_⟩
    simp only [qzTw, scalRep] at hm' ⊢
    rw [← hm', sub_smul, one_smul]
    rfl
  · exact z.2
  · intro g hg
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective g
    have hh : h ∈ Uinf F Ω l := by
      rw [Uinf, cycU, Subgroup.mem_inf, MonoidHom.mem_ker, ← hcomp]
      exact ⟨trivial, hg⟩
    have := congrFun hz ⟨h, hh⟩
    exact this
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DinfNil
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem mem_princ_iff_pow_dvd_sub_one (l : ℕ) [Fact l.Prime] (m : ℕ) (u : ℤ_[l]ˣ) :
    u ∈ KStar.TotallyRealRoots.princ l m ↔ (l : ℤ_[l]) ^ m ∣ (u : ℤ_[l]) - 1 := by
  unfold KStar.TotallyRealRoots.princ KStar.TotallyRealRoots.redPow
  rw [MonoidHom.mem_ker, ← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker,
    map_sub, map_one, sub_eq_zero, Units.ext_iff]
  simp

private theorem pow_succ_dvd_pow_prime_sub_one (l : ℕ) [Fact l.Prime] (j : ℕ) (v : ℤ_[l])
    (h : (l : ℤ_[l]) ^ (j + 1) ∣ v - 1) : (l : ℤ_[l]) ^ (j + 2) ∣ v ^ l - 1 := by
  obtain ⟨c, hc⟩ := h
  have hg : v ^ l - 1 = (v - 1) * ∑ i ∈ Finset.range l, v ^ i := by
    rw [mul_comm, geom_sum_mul]
  have hs : v - 1 ∣ (∑ i ∈ Finset.range l, v ^ i) - l := by
    have e : (∑ i ∈ Finset.range l, v ^ i) - l = ∑ i ∈ Finset.range l, (v ^ i - 1) := by
      rw [Finset.sum_sub_distrib]
      simp
    rw [e]
    exact Finset.dvd_sum fun i _ => by simpa using sub_dvd_pow_sub_pow v 1 i
  obtain ⟨d, hd⟩ := hs
  refine ⟨c + (l : ℤ_[l]) ^ j * c ^ 2 * d, ?_⟩
  have hsum : ∑ i ∈ Finset.range l, v ^ i = l + (v - 1) * d := by linear_combination hd
  rw [hg, hsum, hc]
  ring

private theorem exists_prime_pow_smul_eq_zero_qz (l : ℕ) [Fact l.Prime] (v : QZ l) : ∃ m : ℕ, (l : ℤ_[l]) ^ m • v = 0 := by
  obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective (ZlSub l) v
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt ‖q‖
    (by exact_mod_cast (Fact.out : l.Prime).one_lt : (1 : ℝ) < l)
  refine ⟨m, ?_⟩
  show ((l : ℤ_[l]) ^ m • (Submodule.Quotient.mk q : ℚ_[l] ⧸ ZlSub l)) = 0
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  unfold ZlSub
  refine ⟨(⟨(l : ℚ_[l]) ^ m * q, ?_⟩ : ℤ_[l]), ?_⟩
  · rw [PadicInt.mem_subring_iff, norm_mul, norm_pow, Padic.norm_p, inv_pow, inv_mul_le_iff₀ (pow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) m)]
    simpa using hm.le
  · show (l : ℚ_[l]) ^ m * q = _
    simp [Algebra.smul_def]

private theorem exists_princ_subset_of_mem_nhds_one (l : ℕ) [Fact l.Prime] (V : Set ℤ_[l]ˣ) (hV : V ∈ nhds (1 : ℤ_[l]ˣ)) :
    ∃ n, ∀ u ∈ KStar.TotallyRealRoots.princ l n, u ∈ V := by
  rw [(Units.isOpenEmbedding_val (R := ℤ_[l])).isEmbedding.isInducing.nhds_eq_comap,
    Filter.mem_comap] at hV
  obtain ⟨t, ht, htV⟩ := hV
  rw [Units.val_one, Metric.mem_nhds_iff] at ht
  obtain ⟨ε, εpos, hball⟩ := ht
  have hl1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one εpos hl1
  refine ⟨n, fun u hu => htV (hball ?_)⟩
  rw [mem_princ_iff_pow_dvd_sub_one] at hu
  obtain ⟨c, hc⟩ := hu
  rw [Metric.mem_ball, dist_eq_norm, hc, norm_mul, norm_pow, PadicInt.norm_p]
  calc ((l : ℝ)⁻¹) ^ n * ‖c‖ ≤ ((l : ℝ)⁻¹) ^ n * 1 :=
        mul_le_mul_of_nonneg_left (PadicInt.norm_le_one c) (by positivity)
    _ < ε := by rwa [mul_one]

theorem UpperTheory.V.Kum.dinfNil :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (N : ℕ) (U : Subgroup (G F Ω)) [U.Normal], IsClosed (U : Set (G F Ω)) → ∀ φ ∈ Dinf l N U, (∃ n, ∀ g ∈ levU l U n, funRep ℤ_[l] (QZ l) (cycU l U) g φ = φ) ∧
    ∀ γ ∈ levU l U 1, ∃ k : ℕ, (l : ℤ_[l]) ^ k • φ = 0 ∧ ((funRep ℤ_[l] (QZ l) (cycU l U) γ - 1) ^ k) φ = 0 := by
  intro F Ω _ _ _ _ _ l _ N U _ hU φ hφ
  classical
  have memC : ∀ x : G F Ω, x ∈ cycU l U ↔ x ∈ U ∧ cycZ F Ω l x = 1 := by
    intro x
    unfold cycU
    rw [Subgroup.mem_inf, MonoidHom.mem_ker]
  have memLev : ∀ (m : ℕ) (x : G F Ω),
      x ∈ levU l U m ↔ x ∈ U ∧ cycZ F Ω l x ∈ KStar.TotallyRealRoots.princ l m := by
    intro m x
    unfold levU
    rw [Subgroup.mem_inf, Subgroup.mem_comap]
  have hφ' := hφ
  unfold Dinf XDual at hφ'
  have hlc : IsLocallyConstant φ := hφ'.1
  have hadd : ∀ a b, φ (a * b) = φ a + φ b := hφ'.2.1
  have h1 : φ 1 = 0 := by simpa using hadd 1 1
  have hinv : ∀ a, φ a⁻¹ = - φ a := fun a => by
    have h2 := hadd a⁻¹ a
    rw [inv_mul_cancel, h1] at h2
    exact eq_neg_of_add_eq_zero_left h2.symm
  have hCc : IsClosed (cycU l U : Set (G F Ω)) := by
    have e : (cycU l U : Set (G F Ω)) = (U : Set (G F Ω)) ∩ (cycZ F Ω l) ⁻¹' {1} := by
      ext x
      simp only [SetLike.mem_coe, memC, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    rw [e]
    exact hU.inter (isClosed_singleton.preimage (continuous_cycZ F Ω l))
  have hCcpt : CompactSpace (cycU l U) := isCompact_iff_compactSpace.mp hCc.isCompact
  obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.mp (hlc.isOpen_fiber 0)
  have h1O : (1 : G F Ω) ∈ O := by
    have h2 : (1 : cycU l U) ∈ Subtype.val ⁻¹' O := by
      rw [hOeq]
      exact h1
    exact h2
  obtain ⟨W, hW⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hO h1O
  have hWker : ∀ (d : G F Ω) (hd : d ∈ cycU l U), d ∈ W.toSubgroup → φ ⟨d, hd⟩ = 0 := by
    intro d hd hdW
    have h2 : (⟨d, hd⟩ : cycU l U) ∈ Subtype.val ⁻¹' O := hW hdW
    rw [hOeq] at h2
    exact h2
  have conj_val : ∀ (γ : G F Ω) (x : cycU l U),
      ((conjHom (cycU l U) γ x : cycU l U) : G F Ω) = γ⁻¹ * x * γ := fun _ _ => rfl
  have stabC : ∀ γ ∈ cycU l U, ∀ x, φ (conjHom (cycU l U) γ x) = φ x := by
    intro γ hγ x
    have e : conjHom (cycU l U) γ x = (⟨γ, hγ⟩ : cycU l U)⁻¹ * x * ⟨γ, hγ⟩ :=
      Subtype.ext (by simp only [conj_val, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk])
    rw [e, hadd, hadd, hinv]
    abel
  have stabW : ∀ γ ∈ W.toSubgroup, ∀ x, φ (conjHom (cycU l U) γ x) = φ x := by
    intro γ hγ x
    have hdC : γ⁻¹ * x * γ * (x : G F Ω)⁻¹ ∈ cycU l U :=
      mul_mem (conjHom (cycU l U) γ x).2 (inv_mem x.2)
    have hdW : γ⁻¹ * x * γ * (x : G F Ω)⁻¹ ∈ W.toSubgroup := by
      have h3 : (x : G F Ω) * γ * (x : G F Ω)⁻¹ ∈ W.toSubgroup := W.isNormal'.conj_mem γ hγ x
      have h2 := mul_mem (inv_mem hγ) h3
      simpa [mul_assoc] using h2
    have e : conjHom (cycU l U) γ x = ⟨_, hdC⟩ * x :=
      Subtype.ext (by simp only [conj_val, Subgroup.coe_mul, Subgroup.coe_mk]; group)
    rw [e, hadd, hWker _ hdC hdW, zero_add]
  have stabMul : ∀ a b : G F Ω, (∀ x, φ (conjHom (cycU l U) a x) = φ x) →
      (∀ x, φ (conjHom (cycU l U) b x) = φ x) → ∀ x, φ (conjHom (cycU l U) (a * b) x) = φ x := by
    intro a b ha hb x
    have e : conjHom (cycU l U) (a * b) x = conjHom (cycU l U) b (conjHom (cycU l U) a x) :=
      Subtype.ext (by simp only [conj_val]; group)
    rw [e, hb, ha]
  let S : Set (G F Ω) :=
    ⋃ c : cycU l U, (fun γ => γ * (c : G F Ω)⁻¹) ⁻¹' (W.toSubgroup : Set (G F Ω))
  have hSo : IsOpen S := isOpen_iUnion fun c =>
    W.toOpenSubgroup.isOpen'.preimage (continuous_id.mul continuous_const)
  have hSstab : ∀ γ ∈ S, ∀ x, φ (conjHom (cycU l U) γ x) = φ x := by
    intro γ hγ
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hγ
    have e : γ = (γ * (c : G F Ω)⁻¹) * c := by group
    rw [e]
    exact stabMul _ _ (stabW _ hc) (stabC _ c.2)
  let T : Set (G F Ω) := (U : Set (G F Ω)) ∩ Sᶜ
  have hTc : IsCompact T := (hU.inter hSo.isClosed_compl).isCompact
  have hχT : IsClosed (cycZ F Ω l '' T) := (hTc.image (continuous_cycZ F Ω l)).isClosed
  have h1T : (1 : ℤ_[l]ˣ) ∉ cycZ F Ω l '' T := by
    rintro ⟨t, ⟨htU, htS⟩, ht1⟩
    apply htS
    refine Set.mem_iUnion.mpr ⟨⟨t, (memC t).mpr ⟨htU, ht1⟩⟩, ?_⟩
    show t * t⁻¹ ∈ W.toSubgroup
    rw [mul_inv_cancel]
    exact one_mem _
  obtain ⟨n, hn⟩ := exists_princ_subset_of_mem_nhds_one l _ (hχT.isOpen_compl.mem_nhds h1T)
  have hstab : ∀ g ∈ levU l U n, ∀ x, φ (conjHom (cycU l U) g x) = φ x := by
    intro g hg
    rw [memLev] at hg
    apply hSstab
    by_contra hgS
    exact hn _ hg.2 ⟨g, ⟨hg.1, hgS⟩, rfl⟩
  refine ⟨⟨n, fun g hg => ?_⟩, ?_⟩
  · funext x
    exact hstab g hg x
  intro γ hγ
  have hfin := hlc.range_finite
  choose mf hmf using fun v : QZ l => exists_prime_pow_smul_eq_zero_qz l v
  let k0 := hfin.toFinset.sup mf
  have hk0 : (l : ℤ_[l]) ^ k0 • φ = 0 := by
    funext x
    have hle : mf (φ x) ≤ k0 := Finset.le_sup (hfin.mem_toFinset.mpr ⟨x, rfl⟩)
    rw [Pi.smul_apply, Pi.zero_apply, ← Nat.sub_add_cancel hle, pow_add, mul_smul, hmf, smul_zero]
  set q := l ^ n with hqdef
  have hqpos : 0 < q := pow_pos (Fact.out : l.Prime).pos n
  have hγq : γ ^ q ∈ levU l U n := by
    rw [memLev] at hγ ⊢
    refine ⟨pow_mem hγ.1 q, ?_⟩
    rw [map_pow, mem_princ_iff_pow_dvd_sub_one]
    have key : ∀ j : ℕ, (l : ℤ_[l]) ^ (j + 1) ∣ ((cycZ F Ω l γ ^ (l ^ j) : ℤ_[l]ˣ) : ℤ_[l]) - 1 := by
      intro j
      induction j with
      | zero => simpa [mem_princ_iff_pow_dvd_sub_one] using hγ.2
      | succ j ih =>
        rw [show l ^ (j + 1) = l ^ j * l from pow_succ l j, pow_mul, Units.val_pow_eq_pow_val]
        exact pow_succ_dvd_pow_prime_sub_one l j _ ih
    exact dvd_trans (pow_dvd_pow _ (Nat.le_succ n)) (key n)
  let ρ := funRep ℤ_[l] (QZ l) (cycU l U)
  let Tm : Module.End ℤ_[l] (cycU l U → QZ l) := ρ γ - 1
  let J : Ideal (Polynomial ℤ) :=
    { carrier := {p | Polynomial.aeval Tm p φ = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_add (f := _), LinearMap.add_apply] at *
        rw [ha, hb, add_zero]
      zero_mem' := by simp
      smul_mem' := fun c p hp => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul, Module.End.mul_apply] at *
        rw [hp, map_zero] }
  have hB : (Polynomial.X + 1) ^ q - 1 ∈ J := by
    show (Polynomial.aeval Tm ((Polynomial.X + 1) ^ q - 1)) φ = 0
    simp only [map_sub, map_pow, map_add (f := _), Polynomial.aeval_X, map_one]
    rw [show Tm + 1 = ρ γ from sub_add_cancel _ _, ← map_pow, LinearMap.sub_apply,
      Module.End.one_apply, sub_eq_zero]
    funext x
    exact hstab _ hγq x
  have hL : Polynomial.C ((l : ℤ) ^ k0) ∈ J := by
    show (Polynomial.aeval Tm (Polynomial.C ((l : ℤ) ^ k0))) φ = 0
    rw [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
      Module.End.one_apply, ← Int.cast_smul_eq_zsmul ℤ_[l]]
    push_cast
    exact hk0
  have hP : Polynomial.C (l : ℤ) ∣ (Polynomial.X + 1) ^ q - Polynomial.X ^ q - 1 := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    have hmap : Polynomial.map (Int.castRingHom (ZMod l))
        ((Polynomial.X + 1) ^ q - Polynomial.X ^ q - 1) = 0 := by
      simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_add (f := _), Polynomial.map_X,
        Polynomial.map_one]
      rw [hqdef, add_pow_char_pow, one_pow]
      ring
    have h2 := congrArg (fun P => _root_.AddMonoidAlgebra.coeff (M := ℕ) P i) hmap
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero, eq_intCast] at h2
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h2
  obtain ⟨Qp, hQp⟩ := hP
  have hXq : (Polynomial.X : Polynomial ℤ) ^ q =
      ((Polynomial.X + 1) ^ q - 1) - Polynomial.C (l : ℤ) * Qp := by
    linear_combination (-1 : Polynomial ℤ) * hQp
  have hmem : (Polynomial.X : Polynomial ℤ) ^ (q * k0) ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, pow_mul, map_pow, hXq, map_sub,
      Ideal.Quotient.eq_zero_iff_mem.mpr hB, zero_sub, map_mul]
    calc (-(Ideal.Quotient.mk J (Polynomial.C (l : ℤ)) * Ideal.Quotient.mk J Qp)) ^ k0
        = (-(Ideal.Quotient.mk J Qp)) ^ k0 * Ideal.Quotient.mk J (Polynomial.C ((l : ℤ) ^ k0)) := by
          rw [Polynomial.C_pow, map_pow]
          ring
      _ = 0 := by rw [Ideal.Quotient.eq_zero_iff_mem.mpr hL, mul_zero]
  refine ⟨q * k0, ?_, ?_⟩
  · rw [show q * k0 = (q * k0 - k0) + k0 from
      (Nat.sub_add_cancel (Nat.le_mul_of_pos_left k0 hqpos)).symm, pow_add, mul_smul, hk0, smul_zero]
  · have h2 := hmem
    change (Polynomial.aeval Tm (Polynomial.X ^ (q * k0))) φ = 0 at h2
    rw [map_pow, Polynomial.aeval_X] at h2
    exact h2
end
