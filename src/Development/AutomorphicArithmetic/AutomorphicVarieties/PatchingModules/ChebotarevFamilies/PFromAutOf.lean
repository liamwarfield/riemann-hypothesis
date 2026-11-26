module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.PhiDec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.StableIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ExistsAdjoinCoeffCharacterSubMemMaximalIdealPow

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.CoefficientExtensionPreservesConditionsAndDet
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem l_zero {l : ℕ} [Fact l.Prime] {K : Type} [Field K] [Finite K] (f : ℤ_[l] →+* K) : (l : K) = 0 := by
  by_contra hne
  have hp : (ringChar K).Prime := CharP.char_is_prime K (ringChar K)
  have hlp : ringChar K ≠ l := by
    intro h
    apply hne
    rw [← h]
    exact ringChar.Nat.cast_ringChar
  have hcop : l.Coprime (ringChar K) := (Nat.coprime_primes (Fact.out) hp).mpr hlp.symm
  have hu : IsUnit ((ringChar K : ℕ) : ℤ_[l]) :=
    PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr hcop)
  have hu' := hu.map f
  rw [map_natCast, ringChar.Nat.cast_ringChar] at hu'
  exact not_isUnit_zero hu'

private theorem hom_uniq {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] (f f' : ℤ_[l] →+* R) (h : (l : R) = 0) :
    f = f' := by
  ext x
  have hx := PadicInt.sub_zmodRepr_mem x
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hx
  obtain ⟨y, hy⟩ := hx
  have hx' : x = (PadicInt.zmodRepr x : ℤ_[l]) + y * l := by rw [hy]; ring
  rw [hx', map_add (f := _), map_add (f := _), map_mul, map_mul, map_natCast, map_natCast, map_natCast, map_natCast, h]
  simp

private theorem localization_quotient_separated_dvd {A K L : Type} [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K] [Field L] (g : A →+* L)
    (hi : Function.Injective g) (P : Polynomial A) (hs : (P.map (algebraMap A K)).Separable) :
    (P.map g).Separable := by
  have hP : P.map g = (P.map (algebraMap A K)).map (IsFractionRing.lift hi) := by
    rw [Polynomial.map_map]
    congr 1
    ext a
    simp [IsFractionRing.lift_algebraMap]
  rw [hP]
  exact hs.map

private theorem sep_map {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] (j : A →+* B)
    (hinj : Function.Injective j) (P : Polynomial A) (hs : (P.map (algebraMap A (FractionRing A))).Separable) :
    ((P.map j).map (algebraMap B (FractionRing B))).Separable := by
  rw [Polynomial.map_map]
  exact localization_quotient_separated_dvd (K := FractionRing A) ((algebraMap B (FractionRing B)).comp j)
    ((IsFractionRing.injective B (FractionRing B)).comp hinj) P hs

theorem UpperTheory.V.Pa.Det.coefficientExtension_preserves_conditions_and_det :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x x' : NP F n) (j : x.A →+* x'.A), x.Ext x' j → (∀ D : Subgroup F.G₀, x.N4 D → x'.N4 D) ∧ (x.N3 → x'.N3) ∧ GDet.ofRep (mat x'.ρ) = (GDet.ofRep (mat x.ρ)).map j := by
  intro l _ F n x x' j hE
  obtain ⟨hinj, hloc, hfin, hρ, ha, hψ⟩ := hE
  have hmat : ∀ g, mat x'.ρ g = (mat x.ρ g).map j := by
    intro g
    rw [hρ]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro Dg h4 Z hZ
    obtain ⟨m, b, p, hm, hsum, hlin, hdual, -, -⟩ := UpperTheory.V.Pa.Det.extFree j hinj hloc hfin
    have h0 : ((l : ℕ) : x'.A) = 0 := by
      simpa using congrArg (PowerSeries.C (R := x'.K)) (l_zero (algebraMap ℤ_[l] x'.K))
    have hj : algebraMap ℤ_[l] x'.A = j.comp (algebraMap ℤ_[l] x.A) := hom_uniq _ _ h0
    have heps : ∀ g, ((F.eps ℤ_[l] x'.A g : x'.Aˣ) : x'.A) = j (F.eps ℤ_[l] x.A g : x.Aˣ) := by
      intro g
      simp [GFrame.eps, pushCh, hj]
    have hZi : ∀ i, Z.map (p i) = 0 := by
      intro i
      apply h4
      intro g hg
      have lhs : ∀ (e : x.A) (M : Matrix (Fin n) (Fin n) x.A) a c,
          p i (j e * ∑ k, j (M a k) * Z k c) = e * ∑ k, M a k * p i (Z k c) := by
        intro e M a c
        set_option synthInstance.maxHeartbeats 100000 in
          rw [Finset.mul_sum, map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← mul_assoc, ← map_mul, hlin, mul_assoc]
      have rhs : ∀ (M : Matrix (Fin n) (Fin n) x.A) a c,
          p i (∑ k, Z a k * j (M k c)) = ∑ k, p i (Z a k) * M k c := by
        intro M a c
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [mul_comm, hlin, mul_comm]
      ext a c
      have hac := congrFun (congrFun (hZ g hg) a) c
      simp only [Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul, hmat, Matrix.map_apply, heps] at hac
      simp only [Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul, Matrix.map_apply]
      rw [← lhs, ← rhs, hac]
    ext a c
    have hz : ∀ i, p i (Z a c) = 0 := by
      intro i
      have h1 := congrFun (congrFun (hZi i) a) c
      simpa only [Matrix.map_apply, Matrix.zero_apply] using h1
    rw [hsum (Z a c), Matrix.zero_apply]
    simp [hz]
  · intro h3 U hU hne
    obtain ⟨σ, hσ, hsep⟩ := h3 U hU hne
    refine ⟨σ, hσ, ?_⟩
    rw [hmat, Matrix.charpoly_map]
    exact sep_map j hinj _ hsep
  · apply GDet.ext
    intro B _ _ y
    show Matrix.det _ = Matrix.det _
    congr 1
    simp only [MonoidHom.coe_coe, AlgHom.coe_toRingHom, GDet.repAlg]
    congr 2
    apply congrArg
    ext g a b
    simp [hmat]
    try rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.ThickNonSS
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.thickNonSS :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid F O n} (B : UniversalOrdinaryDeterminantRing r) (q : PrimeSpectrum B.B), B.IsThick q → NonSS (augmentationIdealKernel B.u) (RingHom.id B.B) q.asIdeal := by
  intro l _ F O _ _ _ n r B q h
  have he : augmentationIdealKernel B.u = (B.GroupAlgebraKernelIdeal : Set (MonoidAlgebra B.B F.G₀)) := by
    have : B.u.D.chBar (pairGens B.u) = B.GroupAlgebraKernelIdeal := by
      unfold UniversalOrdinaryDeterminantRing.GroupAlgebraKernelIdeal UniversalOrdinaryDeterminantRing.E0gens GDet.chBar pairGens
      rw [Set.union_assoc]
    unfold augmentationIdealKernel
    rw [this]
    rfl
  refine ⟨B.kap q, inferInstance, B.toKap q, ?_, ?_⟩
  · ext x
    unfold UniversalOrdinaryDeterminantRing.toKap
    rw [RingHom.mem_ker, RingHom.comp_apply, map_eq_zero, Ideal.algebraMap_residueField_eq_zero]
  · rw [RingHom.comp_id, he]
    exact h.2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.TypeIDisc
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

open UpperTheory.V.CA in
private theorem tr_of_map {n : ℕ} {A G K : Type} [CommRing A] [Group G] [CommRing K] (hn : 1 ≤ n)
    (D : GDet n A G) (f : A →+* K) (ρ : G →* Matrix (Fin n) (Fin n) K) (h : D.map f = GDet.ofRep ρ) (g : G) :
    f (D.tr (MonoidAlgebra.single g 1)) = (ρ g).trace := by
  have h1 := ((d_gmap D).2.2.1 f (MonoidAlgebra.single g 1)).2 1
  rw [MonoidAlgebra.mapRingHom_single, map_one, h] at h1
  have h2 := (d_toDet (GDet.ofRep ρ) (MonoidAlgebra.single g 1)).2.2.1
  rw [d_toDet_ofRep.1, (d_ofRep _ _ _).2.2.1 hn] at h2
  have h3 : GDet.repAlg ρ K (MonoidAlgebra.single g 1) = ρ g := by
    ext i j; simp [GDet.repAlg]
  rw [h3] at h2
  exact h1.symm.trans h2.symm

private theorem span_top {n : ℕ} {A L : Type} [CommRing A] [Field L] [Algebra A L] (t : A)
    (ht : algebraMap A L t ≠ 0) (S : Set (Matrix (Fin n) (Fin n) A))
    (hS : ∀ Z, ∃ s : ℕ, t ^ s • Z ∈ Submodule.span A S) :
    Submodule.span L ((algebraMap A L).mapMatrix '' S) = ⊤ := by
  have h1 : ∀ Z ∈ Submodule.span A S, (algebraMap A L).mapMatrix Z ∈
      Submodule.span L ((algebraMap A L).mapMatrix '' S) := by
    intro Z hZ
    induction hZ using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => simp
    | add y z _ _ hy hz =>
      have : (algebraMap A L).mapMatrix (y + z) =
          (algebraMap A L).mapMatrix y + (algebraMap A L).mapMatrix z := by
        ext i j; simp
      rw [this]; exact add_mem hy hz
    | smul c y _ hy =>
      have : (algebraMap A L).mapMatrix (c • y) = algebraMap A L c • (algebraMap A L).mapMatrix y := by
        ext i j; simp
      rw [this]; exact Submodule.smul_mem _ _ hy
  have h2 : ∀ Z : Matrix (Fin n) (Fin n) A, (algebraMap A L).mapMatrix Z ∈
      Submodule.span L ((algebraMap A L).mapMatrix '' S) := by
    intro Z
    obtain ⟨s, hs⟩ := hS Z
    have h := h1 _ hs
    have e : (algebraMap A L).mapMatrix (t ^ s • Z) = algebraMap A L t ^ s • (algebraMap A L).mapMatrix Z := by
      ext i j; simp
    rw [e] at h
    exact (Submodule.smul_mem_iff _ (pow_ne_zero s ht)).1 h
  rw [eq_top_iff]
  intro Z _
  rw [Matrix.matrix_eq_sum_single Z]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  have e : Matrix.single i j (Z i j) = Z i j • (algebraMap A L).mapMatrix (Matrix.single i j (1 : A)) := by
    ext a b
    by_cases h : i = a ∧ j = b <;> simp [Matrix.single_apply, h]
  rw [e]
  exact Submodule.smul_mem _ _ (h2 _)

theorem UpperTheory.V.Pa.Det.typeIDisc :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) {R : Type} [CommRing R] (D : GDet n R F.G₀) (f : R →+* x.A), x.a = n → D.map f = GDet.ofRep (mat x.ρ) → ∀ q : Ideal R, q ≤ RingHom.ker f → DiscSt D q := by
  intro l _ F n x R _ D f ha hD q hq
  have hn : 1 ≤ n := x.a_pos.trans x.a_le
  have ht : algebraMap x.A (FractionRing x.A) x.t ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective x.A (FractionRing x.A))).2 PowerSeries.X_ne_zero
  have hsp := span_top (L := FractionRing x.A) x.t ht (mat x.ρ '' (F.G' : Set F.G₀)) fun Z =>
    x.span Z fun i j => ⟨fun _ => Submodule.mem_top, fun h => (h (by simp [ha])).elim⟩
  obtain ⟨y, hy, hdet⟩ := (UpperTheory.V.CA.g_gram _ _ _).1 hsp
  have hy' : ∀ a, ∃ g, (algebraMap x.A (FractionRing x.A)).mapMatrix (mat x.ρ g) = y a := fun a => by
    obtain ⟨_, ⟨g, -, rfl⟩, h⟩ := hy a
    exact ⟨g, h⟩
  choose g hg using hy'
  refine ⟨fun i => g (finProdFinEquiv.symm i), fun i => g (finProdFinEquiv.symm i), fun hm => hdet ?_⟩
  have h0 := congrArg (algebraMap x.A (FractionRing x.A)) (RingHom.mem_ker.1 (hq hm))
  rw [map_zero, ← RingHom.comp_apply, RingHom.map_det] at h0
  rw [← Matrix.det_submatrix_equiv_self finProdFinEquiv.symm, ← h0]
  congr 1
  ext a b
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, RingHom.comp_apply, tr_of_map hn D f _ hD,
    Matrix.submatrix_apply, Matrix.of_apply, ← hg, ← hg, ← map_mul, ← map_mul, RingHom.mapMatrix_apply]
  exact (AddMonoidHom.map_trace (algebraMap x.A (FractionRing x.A)) _).symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.ConstMap
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.constMap :
    ∀ {K K' : Type} [Field K] [Finite K] [Field K'] (j : PowerSeries K →+* PowerSeries K'), ∃ ι : K →+* K', ∀ a, j (PowerSeries.C a) = PowerSeries.C (ι a) := by
  intro K K' _ _ _ j
  classical
  haveI := Fintype.ofFinite K
  set p := ringChar K with hpdef
  haveI : CharP K p := ringChar.charP K
  obtain ⟨n, hp, hq⟩ := FiniteField.card K p
  haveI : Fact p.Prime := ⟨hp⟩
  set e : K →+* PowerSeries K' := j.comp PowerSeries.C
  haveI : CharP (PowerSeries K') p := charP_of_injective_ringHom e.injective p
  have key : ∀ f : PowerSeries K', f ^ (p ^ (n : ℕ)) = f → f = PowerSeries.C (PowerSeries.constantCoeff f) := by
    intro f hf
    set c := PowerSeries.constantCoeff f with hcdef
    have hc : c ^ (p ^ (n : ℕ)) = c := by
      have h2 := congrArg PowerSeries.constantCoeff hf
      rw [map_pow] at h2
      exact h2
    have hd : (f - PowerSeries.C c) ^ (p ^ (n : ℕ)) = f - PowerSeries.C c := by
      rw [sub_pow_char_pow, hf, ← map_pow, hc]
    have hd0 : PowerSeries.constantCoeff (f - PowerSeries.C c) = 0 := by
      rw [map_sub, PowerSeries.constantCoeff_C, hcdef, sub_self]
    have hq1 : 1 ≤ p ^ (n : ℕ) - 1 := by
      have h1 : 2 ≤ p := hp.two_le
      have h3 : p ≤ p ^ (n : ℕ) := Nat.le_self_pow (PNat.ne_zero n) p
      omega
    have hprod : (f - PowerSeries.C c) * ((f - PowerSeries.C c) ^ (p ^ (n : ℕ) - 1) - 1) = 0 := by
      rw [mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel (by omega), hd, sub_self]
    rcases mul_eq_zero.mp hprod with h | h
    · exact sub_eq_zero.mp h
    · exfalso
      have h4 := congrArg PowerSeries.constantCoeff h
      rw [map_sub, map_pow, hd0, zero_pow (by omega), map_one, map_zero] at h4
      exact zero_ne_one (sub_eq_zero.mp h4)
  refine ⟨PowerSeries.constantCoeff.comp e, fun a => ?_⟩
  have ha : j (PowerSeries.C a) ^ (p ^ (n : ℕ)) = j (PowerSeries.C a) := by
    rw [← map_pow, ← map_pow, ← hq, FiniteField.pow_card]
  exact key _ ha
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.UnipPow
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem charK (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [Finite K] [Algebra ℤ_[l] K] : CharP K l := by
  obtain ⟨p, hp⟩ := CharP.exists K
  haveI := hp
  have hpp : p.Prime := CharP.char_is_prime K p
  by_contra hne
  have hpl : p ≠ l := fun h => hne (h ▸ hp)
  have hu : IsUnit (p : ℤ_[l]) := by
    by_contra h
    rw [PadicInt.not_isUnit_iff, ← Int.cast_natCast, PadicInt.norm_int_lt_one_iff_dvd,
      Int.natCast_dvd_natCast] at h
    exact hpl ((Nat.prime_dvd_prime_iff_eq (Fact.out) hpp).mp h).symm
  have := hu.map (algebraMap ℤ_[l] K)
  rw [map_natCast, CharP.cast_eq_zero] at this
  exact not_isUnit_zero this

private theorem unip_pow (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [CharP K l] (n m : ℕ)
    (M : Matrix (Fin n) (Fin n) (PowerSeries K))
    (hM : (M.map (PowerSeries.constantCoeff : PowerSeries K →+* K)).charpoly = (Polynomial.X - 1) ^ n) (i j : Fin n) :
    (M ^ l ^ (n * m) - 1) i j ∈ maximalIdeal (PowerSeries K) ^ m := by
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · exact (IsEmpty.false i).elim
  haveI : CharP (PowerSeries K) l :=
    charP_of_injective_algebraMap (algebraMap K (PowerSeries K)).injective l
  set N := M - 1 with hN
  have hMN : M = 1 + N := by rw [hN]; abel
  have hfrob : M ^ l ^ (n * m) - 1 = N ^ l ^ (n * m) := by
    rw [hMN, add_pow_char_pow_of_commute (p := l) (h := Commute.one_left N), one_pow, add_sub_cancel_left]
  let f := (PowerSeries.constantCoeff : PowerSeries K →+* K).mapMatrix (m := Fin n)
  have hNn : f (N ^ n) = 0 := by
    rw [map_pow, hN, map_sub, map_one, RingHom.mapMatrix_apply]
    have := Matrix.aeval_self_charpoly (M.map PowerSeries.constantCoeff)
    rw [hM] at this
    simpa [map_pow, map_sub] using this
  have h1 : ∀ a b, (N ^ n) a b ∈ maximalIdeal (PowerSeries K) := by
    intro a b
    have h0 : PowerSeries.constantCoeff ((N ^ n) a b) = 0 := by
      have := congrFun (congrFun hNn a) b
      simpa [f, RingHom.mapMatrix_apply] using this
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff, h0]
    exact not_isUnit_zero
  have hpow : ∀ (I : Ideal (PowerSeries K)) (P : Matrix (Fin n) (Fin n) (PowerSeries K)),
      (∀ a b, P a b ∈ I) → ∀ k : ℕ, ∀ a b, (P ^ k) a b ∈ I ^ k := by
    intro I P hP k
    induction k with
    | zero => intro a b; simp [Ideal.one_eq_top]
    | succ k ih =>
      intro a b
      rw [pow_succ P, Matrix.mul_apply, pow_succ I]
      exact Ideal.sum_mem _ fun c _ => Ideal.mul_mem_mul (ih a c) (hP c b)
  have hle : n * m ≤ l ^ (n * m) := (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le
  rw [hfrob, show l ^ (n * m) = n * m + (l ^ (n * m) - n * m) by omega, pow_add, pow_mul,
    Matrix.mul_apply]
  exact Ideal.sum_mem _ fun c _ => Ideal.mul_mem_right _ _ (hpow _ _ h1 m i c)

theorem UpperTheory.V.Pa.rhoPL :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (H : OpenNormalSubgroup F.Γ), (∀ g ∈ H, ∃ h : F.η g = 1, ((mat x.ρ ⟨g, h⟩).map (PowerSeries.constantCoeff : x.A →+* x.K)).charpoly = (Polynomial.X - 1) ^ n) → ∀ g : F.G₀, (g : F.Γ) ∈ PL l H.toSubgroup → x.ρ g = 1 := by
  intro l _ F n x H hH g hg
  haveI : CharP x.K l := charK l x.K
  have key : ∀ m : ℕ, ∀ i j, (mat x.ρ g - 1) i j ∈ maximalIdeal (PowerSeries x.K) ^ m := by
    intro m
    let φ : F.G₀ →* Matrix (Fin n) (Fin n) (PowerSeries x.K ⧸ maximalIdeal (PowerSeries x.K) ^ m) :=
      (Ideal.Quotient.mk (maximalIdeal (PowerSeries x.K) ^ m)).mapMatrix.toMonoidHom.comp (mat x.ρ)
    have hφ : ∀ y, φ y = 1 ↔ ∀ i j, (mat x.ρ y - 1) i j ∈ maximalIdeal (PowerSeries x.K) ^ m := by
      intro y
      rw [← Matrix.ext_iff]
      refine forall_congr' fun i => forall_congr' fun j => ?_
      rw [Matrix.sub_apply, ← Ideal.Quotient.eq]
      show Ideal.Quotient.mk _ (mat x.ρ y i j) =
          (1 : Matrix (Fin n) (Fin n) (PowerSeries x.K ⧸ maximalIdeal (PowerSeries x.K) ^ m)) i j ↔ _
      rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    let T : Subgroup F.Γ := φ.ker.map F.η.ker.subtype
    have hTopen : IsOpen (T : Set F.Γ) := by
      have hK : IsOpen (φ.ker : Set F.G₀) := by
        have e : (φ.ker : Set F.G₀) = ⋂ i, ⋂ j, {y : F.G₀ | φ y i j =
            (1 : Matrix (Fin n) (Fin n) (PowerSeries x.K ⧸ maximalIdeal (PowerSeries x.K) ^ m)) i j} := by
          ext y
          simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_setOf_eq]
          exact Matrix.ext_iff.symm
        rw [e]
        exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
          (x.cont i j m : IsLocallyConstant fun y : F.G₀ => φ y i j).isOpen_fiber _
      rw [Subgroup.coe_map]
      exact F.η_open.isOpenMap_subtype_val _ hK
    obtain ⟨V, hV⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hTopen T.one_mem
    let W : OpenNormalSubgroup F.Γ :=
      { toSubgroup := T.normalCore
        isOpen' := Subgroup.isOpen_mono (H₁ := V.toSubgroup)
          (Subgroup.normal_le_normalCore.mpr fun a ha => hV ha) V.toOpenSubgroup.isOpen
        isNormal' := Subgroup.normalCore_normal T }
    have hW : ∀ h ∈ H.toSubgroup, ∃ e, h ^ l ^ e ∈ W := by
      intro h hh
      refine ⟨n * m, ?_⟩
      show ∀ b : F.Γ, b * h ^ l ^ (n * m) * b⁻¹ ∈ T
      intro b
      rw [← conj_pow]
      have hbh : b * h * b⁻¹ ∈ H.toSubgroup := H.isNormal'.conj_mem h hh b
      obtain ⟨he, hchar⟩ := hH _ hbh
      refine Subgroup.mem_map.mpr ⟨⟨b * h * b⁻¹, he⟩ ^ l ^ (n * m), ?_, by simp⟩
      rw [MonoidHom.mem_ker, hφ, map_pow]
      exact unip_pow l x.K n m _ hchar
    have hgW : (g : F.Γ) ∈ T.normalCore := by
      have h2 := hg
      simp only [UpperTheory.V.Pa.PL, Subgroup.mem_iInf] at h2
      exact h2 W hW
    have h1 := T.normalCore_le hgW
    obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp h1
    have hyg' : y = g := Subtype.ext hyg
    rw [← hyg']
    exact (hφ y).mp hy
  apply Units.ext
  show mat x.ρ g = 1
  refine Matrix.ext fun i j => ?_
  have h0 : (mat x.ρ g - 1) i j ∈ ⨅ m, maximalIdeal (PowerSeries x.K) ^ m :=
    Submodule.mem_iInf _ |>.mpr fun m => key m i j
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top,
    Ideal.mem_bot, Matrix.sub_apply, sub_eq_zero] at h0
  exact h0
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

namespace UpperTheory.V.Pa

private theorem chi_ofRep {n : ℕ} {A G : Type} [CommRing A] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    (GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly := by
  change (GDet.repAlg ρ (Polynomial A) _).det = _
  rw [map_sub, MonoidAlgebra.mapRingHom_single, Matrix.charpoly]
  congr 1
  ext i j : 2
  by_cases h : i = j <;> simp [GDet.repAlg, Matrix.charmatrix, h, Matrix.one_apply, Matrix.diagonal_apply]

private theorem map_ofRep {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A)
    (f : A →+* B) : (GDet.ofRep ρ).map f = GDet.ofRep (f.mapMatrix.toMonoidHom.comp ρ) := by
  refine GDet.ext fun C _ _ x => ?_
  letI : Algebra A C := ((algebraMap B C).comp f).toAlgebra
  change (GDet.repAlg ρ C x).det = (GDet.repAlg _ C x).det
  congr 2

theorem chain_of (hN : Norm) (hC : Choice) (hP : ArPl) (h1 : FirstOrderDualArithmeticBound) (h2 : TaylorWilesObstructionBound) (hR : Raw) (P : CohP)
    (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
    [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B) (hn : 0 < n) (hS : V0.S' = s.S)
    (hL : LocCFT s) (hμ : ∃ g : V0.frame.G₀, PadicInt.toZMod ((V0.frame.ε g : ℤ_[l]ˣ) : ℤ_[l]) ≠ 1) (hA : HasAut B J)
    (h : ℕ) (x : Fin (h + 1) → Point r) (f : ∀ i, B.B →ₐ[O] (x i).A) (hx : ∀ i, (x i).NiceI ∨ (x i).NiceE)
    (hf : ∀ i, B.IsPt (x i) (f i)) :
    ChainConcl (pairOf B.u) J (fun i => RingHom.ker (f i)) ∧
      ∀ i, (x i).TypeI → ∀ q : Ideal B.B, q ≤ RingHom.ker (f i) → DiscSt B.u.D q := by
  haveI := IsCoef.char (l := l) (O := O)
  haveI := IsCoef.finite (l := l) (O := O)
  haveI := IsCoef.complete (l := l) (O := O)
  obtain ⟨hΦ, hT⟩ := hP P l L Ω s V0 O n r hS
  have hI := (ipEq l L Ω s V0 O n r).1
  choose y j jinj jloc _ jD jψ y3 y4 yI using fun i => hN l V0.frame O n r (x i) (globOf r V0).frame.Iu s.odd hn
    (fun u => ((hI u).2.symm.trans (hI u).1).le) (hx i)
  obtain ⟨q, sg, z, j', k, al, hsg, hE, hcard, hdet, heig⟩ := hC l (globOf r V0).frame n h y s.odd hΦ hμ y3
  obtain ⟨T, ⟨Pl⟩, rfl, hTs⟩ := hT q sg hsg
  obtain rfl : T.sg = sg := funext hTs
  obtain ⟨A⟩ := hA T Pl
  choose ι hι using fun i => Det.constMap ((j' i).comp (j i))
  have hD : ∀ i, GDet.ofRep (mat (z i).ρ) = (GDet.ofRep (mat (x i).ρ)).map ((j' i).comp (j i)) := fun i => by
    exact (Det.coefficientExtension_preserves_conditions_and_det _ _ _ (hE i)).2.2.trans (congrArg (·.map (j' i)) (jD i))
  have hker : ∀ i, ∀ g : V0.frame.G₀, (g : V0.frame.Γ) ∈ PL l T.H.toSubgroup → (z i).ρ g = 1 := fun i => by
    refine rhoPL l (globOf r V0).frame n (z i) T.H fun g hg => ?_
    obtain ⟨e1, e2, -⟩ := (Pl.H_eq g).1 hg
    refine ⟨e1, ?_⟩
    have hcc : (PowerSeries.constantCoeff : (z i).A →+* (z i).K).comp ((j' i).comp (j i)) =
        (ι i).comp PowerSeries.constantCoeff := RingHom.ext fun a => by
      haveI := jloc i
      haveI := (hE i).2.1
      have m1 : ¬ IsUnit (a - PowerSeries.C (PowerSeries.constantCoeff a)) := by
        simp [PowerSeries.isUnit_iff_constantCoeff]
      have m2 : ¬ IsUnit (j' i (j i (a - PowerSeries.C (PowerSeries.constantCoeff a)))) := fun u =>
        m1 (IsLocalHom.map_nonunit _ (IsLocalHom.map_nonunit _ u))
      rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, not_not, map_sub, map_sub, map_sub, sub_eq_zero] at m2
      have m3 := congrArg PowerSeries.constantCoeff (hι i (PowerSeries.constantCoeff a))
      exact m2.trans (m3.trans (PowerSeries.constantCoeff_C _))
    have e3 : (GDet.ofRep (mat (z i).ρ)).map (PowerSeries.constantCoeff : (z i).A →+* (z i).K) =
        r.Dbar.map ((ι i).comp (algebraMap (ResidueField O) (x i).K)) := by
      rw [hD i]
      refine Eq.trans (b := (GDet.ofRep (mat (x i).ρ)).map ((ι i).comp PowerSeries.constantCoeff)) (by rw [← hcc]; rfl) ?_
      exact congrArg (·.map (ι i)) (x i).red
    rw [map_ofRep, Resid.Dbar, map_ofRep] at e3
    have e4 := congrArg (·.chi (MonoidAlgebra.single ⟨g, e1⟩ 1)) e3
    simp only [chi_ofRep] at e4
    refine e4.trans ?_
    have e5 : W.diagRep r.chib ⟨g, e1⟩ = 1 := by
      change Matrix.diagonal _ = _
      simp only [e2, Units.val_one, Matrix.diagonal_one]
    refine (chi_ofRep _ _).trans ?_
    change ((RingHom.mapMatrix ((ι i).comp (algebraMap (ResidueField O) (x i).K))) (W.diagRep r.chib ⟨g, e1⟩)).charpoly = _
    rw [e5, map_one, Matrix.charpoly_one, Fintype.card_fin]
  let pt : ∀ i, Pt T (pairOf B.u) (n * Module.finrank ℚ (Lp L) + n * T.q) := fun i =>
    letI : Algebra O (z i).K := ((ι i).comp (algebraMap O (x i).K)).toAlgebra
    { x := z i
      k := k i
      al := al i
      eig := heig i
      b1 := h1 P l L Ω s V0 O n r T Pl (z i) (k i) (al i) hS hL hμ (hker i)
        ((Det.coefficientExtension_preserves_conditions_and_det _ _ _ (hE i)).1 _ (y4 i)) (heig i) (hdet i)
      b2 := h2 P l L Ω s V0 O n r T Pl (z i) (k i) (al i) hS hμ (hker i) (heig i)
      f := { ((j' i).comp (j i)).comp (f i : B.B →+* (x i).A) with
        commutes' := fun a => by
          change ((j' i).comp (j i)) (f i (algebraMap O B.B a)) = _
          rw [AlgHom.commutes]
          rw [PowerSeries.algebraMap_apply, PowerSeries.algebraMap_apply]
          exact hι i _ }
      maps := ⟨by rw [hD i, ← (hf i).1]; rfl, fun v a => by
        rw [(hE i).2.2.2.2.2 v a, jψ i v a, ← (hf i).2 v a]; rfl⟩ }
  have hk : ∀ i, RingHom.ker (pt i).f = RingHom.ker (f i) := fun i => by
    ext b
    change j' i (j i (f i b)) = 0 ↔ f i b = 0
    rw [map_eq_zero_iff _ (hE i).1, map_eq_zero_iff _ (jinj i)]
  refine ⟨?_, fun i hi q hq => ?_⟩
  · have := hR l _ (globOf r V0) T n O (residOf r) B.B (pairOf B.u) J _ A s.odd
      ⟨fun g hg a => ((Pl.H_eq g).1 hg).2.1 a, fun u => (hI u).2⟩
      (fun N b => by
        obtain ⟨c, hc, hb⟩ := CA.exists_adjoin_coeff_character_sub_mem_maximalIdeal_pow r B N b
        refine ⟨c, Algebra.adjoin_mono ?_ hc, hb⟩
        rintro _ (⟨a, g, -, -, rfl⟩ | e)
        · exact Or.inl ⟨a, g, rfl⟩
        · exact Or.inr e) h pt hcard
    simpa only [hk] using this
  · exact Det.typeIDisc (z i) B.u.D (((j' i).comp (j i)).comp (f i : B.B →+* (x i).A)) ((hE i).2.2.2.2.1.trans (yI i hi)) (pt i).maps.1 q (hq.trans (hk i).ge)

theorem pFromAut_of (hN : Norm) (hC : Choice) (hP : ArPl) (h1 : FirstOrderDualArithmeticBound) (h2 : TaylorWilesObstructionBound) (hR : Raw) : PfromAut := by
  intro P l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ _ _ n r B J hn hS hL hμ hA
  have key := chain_of hN hC hP h1 h2 hR P l L Ω s V0 O n r B J hn hS hL hμ hA
  have hE : augmentationIdealKernel (pairOf B.u) = augmentationIdealKernel B.u := by
    rw [(ipEq l L Ω s V0 O n r).2 B]
    ext z
    simp only [augmentationIdealKernel, UniversalOrdinaryDeterminantRing.GroupAlgebraKernelIdeal, GDet.chBar, pairGens, UniversalOrdinaryDeterminantRing.E0gens, Set.mem_setOf_eq, Set.union_assoc]
  refine ⟨fun x f hx hf hJ q hq => ?_, fun h x f e hx hf he h₁ q hq hs => ?_⟩
  · obtain ⟨k1, k2⟩ := key 0 (fun _ => x) (fun _ => f) (fun _ => Or.inl hx) fun _ => hf
    exact k1 Fin.elim0 (fun i => i.elim0) ⟨_, RingHom.ker_isPrime f, k2 0 hx.2.1 _ le_rfl, hJ, le_rfl⟩ q.asIdeal q.isPrime hq
      (Or.inl (k2 0 hx.2.1 _ hq))
  · obtain ⟨k1, -⟩ := key h x f (fun i => Or.inr (hx i)) hf
    obtain ⟨q₁, a1, a2, a3⟩ := h₁
    refine k1 (fun i => (e i).asIdeal) (fun i => ⟨(e i).isPrime, hE ▸ Det.thickNonSS B _ (he i).1, (he i).2⟩)
      ⟨_, q₁.isPrime, (Det.stableIff B _).1 a1, a2, a3⟩ q.asIdeal q.isPrime hq ?_
    exact hs.imp (Det.stableIff B _).1 fun t => hE ▸ Det.thickNonSS B _ t

end UpperTheory.V.Pa
