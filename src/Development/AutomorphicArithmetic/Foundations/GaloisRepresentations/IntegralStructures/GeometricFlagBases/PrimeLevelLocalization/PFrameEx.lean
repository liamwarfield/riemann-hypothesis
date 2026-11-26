module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNormHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.MuHomSingle
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.TrivOfLe
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.ValLeOneOfForall

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PIntCof
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

private theorem mem_GLint_of_entries {K : Type} [Field K] {n : ℕ} (O : Subring K) (g : GL (Fin n) K)
    (h1 : ∀ a b, g.val a b ∈ O) (h2 : ∀ a b, (g⁻¹).val a b ∈ O) : g ∈ Formalism.UG.GLint (Fin n) O := by
  have inj : Function.Injective (O.subtype.mapMatrix (m := Fin n)) :=
    fun A B h => by ext i j; exact congrFun (congrFun h i) j
  let A : Matrix (Fin n) (Fin n) O := fun i j => ⟨g.val i j, h1 i j⟩
  let B : Matrix (Fin n) (Fin n) O := fun i j => ⟨(g⁻¹).val i j, h2 i j⟩
  have hA : O.subtype.mapMatrix A = g.val := rfl
  have hB : O.subtype.mapMatrix B = (g⁻¹).val := rfl
  refine ⟨⟨A, B, inj ?_, inj ?_⟩, Units.ext rfl⟩
  · rw [map_mul, hA, hB, map_one, Units.mul_inv]
  · rw [map_mul, hA, hB, map_one, Units.inv_mul]

theorem UpperTheory.Gal.W2.Seed.pIntCof :
    IntCof := by
  intro E _ _ n a
  have key : ∀ x : Af E, ∀ᶠ w : Plc E in Filter.cofinite, pLoc E w x ∈ w.adicCompletionIntegers E :=
    fun x => x.2
  have h1 := Filter.eventually_all.2 (fun i => Filter.eventually_all.2 (fun j => key (a.val i j)))
  have h2 := Filter.eventually_all.2 (fun i => Filter.eventually_all.2 (fun j => key ((a⁻¹).val i j)))
  filter_upwards [h1, h2] with w ha hb
  refine mem_GLint_of_entries (w.adicCompletionIntegers E).toSubring _ (fun i j => ha i j) (fun i j => ?_)
  rw [← map_inv]
  exact hb i j
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PEvEx
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open GlobalTheory.LFun (KGL)
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

namespace UpperTheory.Gal.W2.Seed

theorem pEvEx : EvEx := by
  intro p E _ _ _ T w hw
  have hk : RingHom.ker T.Φ ≤ RingHom.ker (pLoc E w) := by
    intro x hx
    exact RingHom.mem_ker.2 (((T.Φ_ker x).1 (RingHom.mem_ker.1 hx)) w hw)
  refine ⟨RingHom.liftOfSurjective T.Φ T.Φ_surj ⟨pLoc E w, hk⟩, fun x => ?_⟩
  exact RingHom.liftOfRightInverse_comp_apply _ _ _ ⟨pLoc E w, hk⟩ x

end UpperTheory.Gal.W2.Seed
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PAdTensor
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct

noncomputable section

namespace UpperTheory.Gal.W2.Seed

open GlobalTheory.SplitPts (conjE)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap below)
open GroundTheory.Global.SemiLocal (completionMap)

private theorem eq_zero_of_small {E : Type} [Field E] [NumberField E] {w : Plc E}
    (z : w.adicCompletion E) (h : ∀ n : ℕ, Valued.v z ≤ WithZero.exp (-(n : ℤ))) : z = 0 := by
  by_contra hz
  have h0 : Valued.v z ≠ 0 := (Valuation.ne_zero_iff _).2 hz
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v z = WithZero.exp m :=
    ⟨WithZero.log _, (WithZero.exp_log h0).symm⟩
  have := h (1 - m).toNat
  rw [hm, WithZero.exp_le_exp] at this
  omega

private theorem valued_completionMap_le {E : Type} [Field E] [NumberField E] (P : Plc E)
    (t : (below ℚ P).adicCompletion ℚ) (n : ℕ) (ht : Valued.v t ≤ WithZero.exp (-(n : ℤ))) :
    Valued.v (completionMap (below ℚ P) P t) ≤ WithZero.exp (-(n : ℤ)) := by
  have he : P.asIdeal.ramificationIdx (𝓞 ℚ) ≠ 0 := by
    intro h0
    have h := GroundTheory.Global.SemiLocal.valued_completionMap (below ℚ P) P
      (0 : (below ℚ P).adicCompletion ℚ)
    rw [map_zero, map_zero, map_zero, h0, pow_zero] at h
    exact zero_ne_one h
  rw [GroundTheory.Global.SemiLocal.valued_completionMap]
  refine le_trans ?_ ht
  refine pow_le_of_le_one zero_le (ht.trans ?_) he
  rw [← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

private theorem ringHom_eq {E : Type} [Field E] [NumberField E] (P : Plc E) (v : Plc ℚ)
    (φ ψ : v.adicCompletion ℚ →+* P.adicCompletion E)
    (hφ : ∀ (n : ℕ) (a : v.adicCompletion ℚ), Valued.v a ≤ WithZero.exp (-(n : ℤ)) →
      Valued.v (φ a) ≤ WithZero.exp (-(n : ℤ)))
    (hψ : ∀ (n : ℕ) (a : v.adicCompletion ℚ), Valued.v a ≤ WithZero.exp (-(n : ℤ)) →
      Valued.v (ψ a) ≤ WithZero.exp (-(n : ℤ))) (x : v.adicCompletion ℚ) : φ x = ψ x := by
  have aux : ∀ q : ℚ →+* v.adicCompletion ℚ, DenseRange q → φ x = ψ x := by
    intro q hd
    rw [← sub_eq_zero]
    refine eq_zero_of_small _ fun n => ?_
    have hopen : IsOpen {y : v.adicCompletion ℚ | Valued.v (y - x) ≤ WithZero.exp (-(n : ℤ))} :=
      (GlobalTheory.Idele.isOpen_valued_le (K := ℚ) v (-(n : ℤ))).preimage
        (continuous_id.sub continuous_const)
    obtain ⟨k, hk⟩ := hd.exists_mem_open hopen ⟨x, by simp⟩
    have hk' : Valued.v (q k - x) ≤ WithZero.exp (-(n : ℤ)) := by
      simpa only [Set.mem_ofPred_eq] using hk
    have h : φ (q k) = ψ (q k) := RingHom.congr_fun (Subsingleton.elim (φ.comp q) (ψ.comp q)) k
    have e : φ x - ψ x = ψ (q k - x) - φ (q k - x) := by
      rw [map_sub φ, map_sub ψ, h]
      abel
    rw [e]
    exact (Valuation.map_sub _ _ _).trans (max_le (hψ n _ hk') (hφ n _ hk'))
  exact aux _ (HeightOneSpectrum.denseRange_algebraMap (K := ℚ) v)

private theorem locMap_eq {E : Type} [Field E] [NumberField E] (P : Plc E)
    (x : (below ℚ P).adicCompletion ℚ) :
    GlobalTheory.AdeleBaseChange.locMap ℚ P x = completionMap (below ℚ P) P x :=
  ringHom_eq P (below ℚ P) (GlobalTheory.AdeleBaseChange.locMap ℚ P) (completionMap (below ℚ P) P)
    (fun n a ha => GlobalTheory.AdeleBaseChange.locMap_valued P n a ha)
    (fun n a ha => valued_completionMap_le P a n ha) x

private theorem ringHom_eq_of_continuous {R : Type} [Ring R] [TopologicalSpace R] [T2Space R]
    (v : Plc ℚ) (φ ψ : v.adicCompletion ℚ →+* R) (hφ : Continuous φ) (hψ : Continuous ψ)
    (x : v.adicCompletion ℚ) : φ x = ψ x := by
  have aux : ∀ q : ℚ →+* v.adicCompletion ℚ, DenseRange q → φ x = ψ x := fun q hd =>
    congrFun (hd.equalizer hφ hψ (funext fun k =>
      RingHom.congr_fun (Subsingleton.elim (φ.comp q) (ψ.comp q)) k)) x
  exact aux _ (HeightOneSpectrum.denseRange_algebraMap (K := ℚ) v)

private theorem adMap_eq {E : Type} [Field E] [NumberField E] (a : AfQ) :
    GlobalTheory.AdeleBaseChange.adMap ℚ E a = finiteAdeleMap ℚ E a :=
  FiniteAdeleRing.ext _ fun P => locMap_eq P _

private theorem below_conjSrc {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Plc E) :
    below ℚ (conjSrc (conjE E) w) = below ℚ w := by
  have h := conjPl_conjSrc (conjE E) w
  refine HeightOneSpectrum.ext (Ideal.ext fun y => ?_)
  change algebraMap (𝓞 ℚ) (𝓞 E) y ∈ (conjSrc (conjE E) w).asIdeal ↔ algebraMap (𝓞 ℚ) (𝓞 E) y ∈ w.asIdeal
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E), ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E), ← h]
  have : conjE E ((algebraMap (𝓞 ℚ) (𝓞 E) y : 𝓞 E) : E) = ((algebraMap (𝓞 ℚ) (𝓞 E) y : 𝓞 E) : E) := by
    change conjE E (algebraMap ℚ E (y : ℚ)) = algebraMap ℚ E (y : ℚ)
    simp [eq_ratCast]
  rw [this]

private theorem conj_finiteAdeleMap {E : Type} [Field E] [NumberField E] [IsCMField E] (a : AfQ) :
    conjFin (conjE E) (finiteAdeleMap ℚ E a) = finiteAdeleMap ℚ E a := by
  refine GlobalTheory.EulerTw.pLoc_ext E fun w => ?_
  rw [pLoc_conjFin]
  have hb := below_conjSrc w
  have key : ∀ (u : Plc E) (_ : below ℚ u = below ℚ w) (f : u.adicCompletion E →+* w.adicCompletion E),
      Continuous f → f (pLoc E u (finiteAdeleMap ℚ E a)) = pLoc E w (finiteAdeleMap ℚ E a) := by
    intro u hu f hf
    haveI : w.asIdeal.LiesOver (below ℚ u).asIdeal := (GroundTheory.Global.AdeleBaseChange.below_eq_iff w _).1 hu.symm
    change f (completionMap (below ℚ u) u (a (below ℚ u))) = completionMap (below ℚ w) w (a (below ℚ w))
    rw [← GroundTheory.Global.AdeleBaseChange.completionMap_congr hu w a]
    exact ringHom_eq_of_continuous (below ℚ u) (f.comp (completionMap (below ℚ u) u)) (completionMap (below ℚ u) w)
      (hf.comp (GroundTheory.Global.SemiLocal.continuous_completionMap _ _))
      (GroundTheory.Global.SemiLocal.continuous_completionMap _ _) _
  exact key _ hb _ (conjLoc_spec (conjE E) w).1

end UpperTheory.Gal.W2.Seed

open GlobalTheory.SplitPts (conjE)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap)

theorem UpperTheory.Gal.W2.Seed.pAdTensor :
    AdTensor := by
  intro E _ _ _
  obtain ⟨ι, hι⟩ := GlobalTheory.AdeleBaseChange.exists_toAd ℚ E
  let c : AfQ ⊗[ℚ] E ≃+* Formalism.L2.DIV.AfE ℚ E :=
    (Algebra.TensorProduct.comm ℚ AfQ E).toRingEquiv
  have hc : ∀ a x, c (a ⊗ₜ[ℚ] x) = x ⊗ₜ[ℚ] a := fun a x => rfl
  have hc' : ∀ a x, c.symm (x ⊗ₜ[ℚ] a) = a ⊗ₜ[ℚ] x := fun a x => rfl
  let j := c.trans (RingEquiv.ofBijective ι
    ⟨GlobalTheory.AdeleBaseChange.map_injective hι, GlobalTheory.AdeleBaseChange.map_surjective hι⟩)
  have hj : ∀ y, j y = ι (c y) := fun y => rfl
  refine ⟨j, fun a x => ?_, fun y => ⟨fun hy => ?_, fun hy => ?_⟩, conj_finiteAdeleMap⟩
  · rw [hj, hc, hι, adMap_eq, mul_comm]
  · have : j y ∈ Formalism.UG.intAd E := by
      induction hy using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨a, x, ha, rfl⟩ := hy
        rw [hj, hc]
        exact GlobalTheory.AdeleBaseChange.map_mem_int hι (Formalism.UG.P.levelaf_tmul_mem x ha)
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | neg x _ hx => rw [map_neg]; exact neg_mem hx
    exact this
  · have h : c y ∈ Formalism.L2.DIV.RInt ℚ E := GlobalTheory.AdeleBaseChange.mem_int_of_map hι hy
    obtain ⟨m, g, hg⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)
    obtain ⟨r, hr, e⟩ := Formalism.UG.P.levelaf_decomp g hg h
    have e' : y = c.symm (c y) := (c.symm_apply_apply y).symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e', e, map_sum]
    refine sum_mem fun i _ => AddSubgroup.subset_closure ⟨r i, g i, hr i, ?_⟩
    rw [hc']
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.UptsExt
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct

private theorem upts_ext {C : Type} [Ring C] [Algebra ℚ C] [Nontrivial C] {star : C →+* Cᵐᵒᵖ} {R : Type} [CommRing R] [Algebra ℚ R]
    (x y : UPts star R) (h : (((x : (R ⊗[ℚ] C)ˣ × Rˣ).1 : (R ⊗[ℚ] C)ˣ) : R ⊗[ℚ] C) = ((y : (R ⊗[ℚ] C)ˣ × Rˣ).1 : (R ⊗[ℚ] C)ˣ)) :
    x = y := by
  obtain ⟨⟨g, c⟩, hx⟩ := x
  obtain ⟨⟨g', c'⟩, hy⟩ := y
  have hx' : (g : R ⊗[ℚ] C) * (starT star R g).unop = algebraMap R (R ⊗[ℚ] C) c := hx
  have hy' : (g' : R ⊗[ℚ] C) * (starT star R g').unop = algebraMap R (R ⊗[ℚ] C) c' := hy
  have hg : g = g' := Units.ext h
  subst hg
  have hinj : Function.Injective (algebraMap R (R ⊗[ℚ] C)) := fun a b hab =>
    Algebra.TensorProduct.includeLeft_injective (R := ℚ) (S := ℚ) (A := R) (B := C) (algebraMap ℚ C).injective hab
  have hc : c = c' := Units.ext (hinj (hx'.symm.trans hy'))
  subst hc
  rfl

theorem UpperTheory.Gal.W2.Seed.pTrEx :
    AdTEx → MuEx → IsoEx' → JEx → JEq → JSurj → TrEx := by
  intro hT hM hI hJ hQ hS E _ _ _ A n p _ S hn
  obtain ⟨T⟩ := hT p E
  obtain ⟨μ, hμ⟩ := hM (AfP p) E n
  obtain ⟨a, ha⟩ := hI E A n hn
  obtain ⟨j, hj1, hj2⟩ := hJ E A n p S T μ hμ a ha
  obtain ⟨hc, he⟩ := hQ E A n p S T μ hμ a j hj1
  choose sec hs1 hs2 using hS E A n p S T μ hμ a ha
  have hjs : ∀ h, j (sec h) = h := fun h =>
    upts_ext _ _ (μ.injective ((hj1 (sec h)).trans (hs1 h).symm))
  have hmul : ∀ h h', sec (h * h') = sec h * sec h' := by
    intro h h'
    apply hc
    intro w
    by_cases hw : (p : 𝓞 E) ∈ w.asIdeal
    · rw [map_mul, hs2 _ w hw, hs2 _ w hw, hs2 _ w hw, one_mul]
    · exact (he _ _).1 (by rw [map_mul, hjs, hjs, hjs]) w hw
  exact ⟨{ T with
    μ := μ, mu := hμ, a := a, iso := ha, j := j, j_mx := hj1, j_sim := hj2
    sec := MonoidHom.mk' sec hmul, j_sec := hjs, sec_p := hs2, j_eq := he }⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PJSurj
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open GlobalTheory.SplitPts (conjE)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap)
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Seed

section Core
variable {R R' : Type} [CommRing R] [CommRing R'] {n : ℕ}

private theorem mulG {ε : R} (he : ε * ε = ε) (A B : Matrix (Fin n) (Fin n) R) :
    ((1 - ε) • A + ε • (1 : Matrix (Fin n) (Fin n) R)) * ((1 - ε) • B + ε • (1 : Matrix (Fin n) (Fin n) R)) =
      (1 - ε) • (A * B) + ε • (1 : Matrix (Fin n) (Fin n) R) := by
  have h1 : (1 - ε) * (1 - ε) = 1 - ε := by linear_combination he
  have h2 : (1 - ε) * ε = 0 := by linear_combination -he
  have h3 : ε * (1 - ε) = 0 := by linear_combination -he
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_one, Matrix.one_mul, h1, h2, h3, he,
    zero_smul, add_zero, zero_add]

private theorem smul_eq_of_map (Φ : R →+* R') {ε : R} (hker : ∀ z, Φ z = 0 → (1 - ε) * z = 0)
    {M N : Matrix (Fin n) (Fin n) R} (h : M.map Φ = N.map Φ) : (1 - ε) • M = (1 - ε) • N := by
  ext i k
  have hik : Φ (M i k - N i k) = 0 := by
    have := congrFun (congrFun h i) k
    simp only [Matrix.map_apply] at this
    rw [map_sub, this, sub_self]
  have := hker _ hik
  simp only [Matrix.smul_apply, smul_eq_mul]
  linear_combination this

private theorem inv_part (Φ : R →+* R') {ε : R} (he : ε * ε = ε) (hker : ∀ z, Φ z = 0 → (1 - ε) * z = 0)
    {a a' Y Y' : Matrix (Fin n) (Fin n) R} (haa : a * a' = 1) (ha' : a' * a = 1)
    (hYY : Y.map Φ * Y'.map Φ = 1) :
    ((1 - ε) • (a' * Y * a) + ε • (1 : Matrix (Fin n) (Fin n) R)) *
      ((1 - ε) • (a' * Y' * a) + ε • (1 : Matrix (Fin n) (Fin n) R)) = 1 := by
  rw [mulG he]
  have h1 : (a' * Y * a * (a' * Y' * a)).map Φ = (1 : Matrix (Fin n) (Fin n) R).map Φ := by
    have e : a' * Y * a * (a' * Y' * a) = a' * Y * (a * a') * Y' * a := by simp only [Matrix.mul_assoc]
    have hA : a'.map Φ * a.map Φ = 1 := by
      rw [← Matrix.map_mul, ha', Matrix.map_one _ (map_zero Φ) (map_one Φ)]
    rw [e, haa, Matrix.mul_one, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.mul_assoc (a'.map Φ), hYY,
      Matrix.mul_one, hA, Matrix.map_one _ (map_zero Φ) (map_one Φ)]
  rw [smul_eq_of_map Φ hker h1, ← add_smul, sub_add_cancel, one_smul]

private theorem star_part (Φ : R →+* R') (σ : R →+* R) (σ' : R' →+* R') {ε t : R}
    (hσ : ∀ x, Φ (σ x) = σ' (Φ x)) (he : ε * ε = ε) (hσe : σ ε = ε)
    (hker : ∀ z, Φ z = 0 → (1 - ε) * z = 0)
    {a a' D Y : Matrix (Fin n) (Fin n) R} (haa : a * a' = 1) (ha' : a' * a = 1)
    (hD : (a.map σ)ᵀ * D * a = 1)
    (hX : ((Y.map Φ).map σ')ᵀ * D.map Φ * Y.map Φ = Φ t • D.map Φ) :
    ((((1 - ε) • (a' * Y * a) + ε • (1 : Matrix (Fin n) (Fin n) R))).map σ)ᵀ *
      ((1 - ε) • (a' * Y * a) + ε • (1 : Matrix (Fin n) (Fin n) R)) =
      ((1 - ε) * t + ε) • (1 : Matrix (Fin n) (Fin n) R) := by
  have hGs : ((((1 - ε) • (a' * Y * a) + ε • (1 : Matrix (Fin n) (Fin n) R))).map σ)ᵀ =
      (1 - ε) • ((a' * Y * a).map σ)ᵀ + ε • (1 : Matrix (Fin n) (Fin n) R) := by
    ext i k
    simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul,
      map_sub, map_one, hσe]
    rcases eq_or_ne i k with rfl | h
    · simp
    · simp [Matrix.one_apply, h, h.symm]
  rw [hGs, mulG he]
  have hab : (a'.map σ)ᵀ * (a.map σ)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, haa, Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]
  have hDa : D * a = (a'.map σ)ᵀ := by
    have : (a'.map σ)ᵀ * ((a.map σ)ᵀ * D * a) = (a'.map σ)ᵀ := by rw [hD, Matrix.mul_one]
    rwa [Matrix.mul_assoc ((a.map σ)ᵀ), ← Matrix.mul_assoc, hab, Matrix.one_mul] at this
  have hD2 : (a'.map σ)ᵀ * a' = D := by rw [← hDa, Matrix.mul_assoc, haa, Matrix.mul_one]
  have e1 : ((a' * Y * a).map σ)ᵀ * (a' * Y * a) = (a.map σ)ᵀ * ((Y.map σ)ᵀ * D * Y) * a := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul, ← hD2]
    simp only [Matrix.mul_assoc]
  have hS : ∀ M : Matrix (Fin n) (Fin n) R, ((M.map σ)ᵀ).map Φ = ((M.map Φ).map σ')ᵀ := by
    intro M
    ext i k
    simp [Matrix.map_apply, Matrix.transpose_apply, hσ]
  have h1 : (((a' * Y * a).map σ)ᵀ * (a' * Y * a)).map Φ = (t • (1 : Matrix (Fin n) (Fin n) R)).map Φ := by
    have h2 : ((a.map σ)ᵀ * D * a).map Φ = (1 : Matrix (Fin n) (Fin n) R).map Φ := by rw [hD]
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_one _ (map_zero Φ) (map_one Φ)] at h2
    have h3 : (t • (1 : Matrix (Fin n) (Fin n) R)).map Φ = Φ t • (1 : Matrix (Fin n) (Fin n) R') := by
      ext i k
      rcases eq_or_ne i k with rfl | h
      · simp
      · simp [Matrix.one_apply, h]
    rw [e1, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, hS Y, hX, h3, Matrix.mul_smul, Matrix.smul_mul, h2]
  rw [smul_eq_of_map Φ hker h1, smul_smul, ← add_smul]

private theorem conj_part (Φ : R →+* R') {ε : R} (hΦe : Φ ε = 0)
    {a a' Y : Matrix (Fin n) (Fin n) R} (haa : a * a' = 1) (ha' : a' * a = 1) :
    (a * ((1 - ε) • (a' * Y * a) + ε • (1 : Matrix (Fin n) (Fin n) R)) * a').map Φ = Y.map Φ := by
  have e : a * ((1 - ε) • (a' * Y * a) + ε • (1 : Matrix (Fin n) (Fin n) R)) * a' = (1 - ε) • Y + ε • (1 : Matrix (Fin n) (Fin n) R) := by
    have e1 : a * (a' * Y * a) * a' = Y := by
      calc a * (a' * Y * a) * a' = (a * a') * Y * (a * a') := by simp only [Matrix.mul_assoc]
        _ = Y := by rw [haa, Matrix.one_mul, Matrix.mul_one]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, e1, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, haa]
  rw [e]
  ext i k
  simp [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, hΦe]

end Core

section Applications
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime]

private theorem mem_conj_iff (p : ℕ) (w : Plc E) :
    (p : 𝓞 E) ∈ (conjSrc (conjE E) w).asIdeal ↔ (p : 𝓞 E) ∈ w.asIdeal := by
  have key : ∀ u : Plc E, (p : 𝓞 E) ∈ u.asIdeal ↔
      (p : 𝓞 (maximalRealSubfield E)) ∈ (u.under (𝓞 (maximalRealSubfield E))).asIdeal := by
    intro u
    show _ ↔ algebraMap _ (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ u.asIdeal
    simp
  rw [key, key, GlobalTheory.LocInj.under_conjSrc]

private theorem mx_mem (S : Setup A n p) (h : S.G.GAf) :
    S.mx h * (starT (hermStar (A.H n) (A.det_ne n)) (AfP p) (S.mx h)).unop =
      ((uSimR (AfP p) h : (AfP p)ˣ) : AfP p) ⊗ₜ[ℚ] (1 : Matrix (Fin n) (Fin n) E) := h.2

private theorem mx_inv (S : Setup A n p) (h : S.G.GAf) : S.mx h * S.mx h⁻¹ = 1 :=
  Units.mul_inv (h : (AfP p ⊗[ℚ] S.G.C)ˣ × (AfP p)ˣ).1

private theorem mx_inv' (S : Setup A n p) (h : S.G.GAf) : S.mx h⁻¹ * S.mx h = 1 :=
  Units.inv_mul (h : (AfP p ⊗[ℚ] S.G.C)ˣ × (AfP p)ˣ).1

end Applications

end UpperTheory.Gal.W2.Seed

theorem UpperTheory.Gal.W2.Seed.pJSurj :
    IdemP → MuStar → JSurj := by
  intro hI hM E _ _ _ A n p _ S T μ hμ a ha h
  obtain ⟨e, heQ, heE⟩ := hI p E
  have heeQ : e * e = e := by
    refine RestrictedProduct.ext _ _ fun v => ?_
    show e v * e v = e v
    by_cases hv : (p : 𝓞 ℚ) ∈ v.asIdeal
    · rw [(heQ v).1 hv, one_mul]
    · rw [(heQ v).2 hv, zero_mul]
  have hρe : T.ρ e = 0 := (T.ker e).2 fun v hv => (heQ v).2 hv
  have hkerQ : ∀ z, T.ρ z = 0 → (1 - e) * z = 0 := by
    intro z hz
    have hz' := (T.ker z).1 hz
    refine RestrictedProduct.ext _ _ fun v => ?_
    show (1 - e v) * z v = 0
    by_cases hv : (p : 𝓞 ℚ) ∈ v.asIdeal
    · rw [(heQ v).1 hv, sub_self, zero_mul]
    · rw [hz' v hv, mul_zero]
  obtain ⟨ε, hε⟩ : ∃ ε : Af E, ε = finiteAdeleMap ℚ E e := ⟨_, rfl⟩
  rw [← hε] at heE
  have heps : ε * ε = ε := by rw [hε, ← map_mul, heeQ]
  have hΦe : T.Φ ε = 0 := by rw [hε, T.Φ_Q, hρe, TensorProduct.zero_tmul]
  have hker : ∀ z, T.Φ z = 0 → (1 - ε) * z = 0 := by
    intro z hz
    have hz' := (T.Φ_ker z).1 hz
    refine GlobalTheory.EulerTw.pLoc_ext E fun w => ?_
    rw [map_mul, map_sub, map_one, map_zero]
    by_cases hw : (p : 𝓞 E) ∈ w.asIdeal
    · rw [(heE w).1 hw, sub_self, zero_mul]
    · rw [hz' w hw, mul_zero]
  have hσe : conjFin (conjE E) ε = ε := by
    refine GlobalTheory.EulerTw.pLoc_ext E fun w => ?_
    rw [pLoc_conjFin]
    by_cases hw : (p : 𝓞 E) ∈ w.asIdeal
    · rw [(heE _).1 ((mem_conj_iff p w).2 hw), (heE w).1 hw, map_one]
    · rw [(heE _).2 (mt (mem_conj_iff p w).1 hw), (heE w).2 hw, map_zero]
  obtain ⟨c, hc⟩ : ∃ c : (AfP p)ˣ, c = uSimR (AfP p) h := ⟨_, rfl⟩
  obtain ⟨s0, hs0⟩ := T.surj (c : AfP p)
  obtain ⟨s1, hs1⟩ := T.surj ((c⁻¹ : (AfP p)ˣ) : AfP p)
  obtain ⟨X, hXd⟩ : ∃ X, X = μ (S.mx h) := ⟨_, rfl⟩
  obtain ⟨X', hXd'⟩ : ∃ X', X' = μ (S.mx h⁻¹) := ⟨_, rfl⟩
  obtain ⟨Xs, hXsd⟩ : ∃ Xs, Xs = μ (starT (hermStar (A.H n) (A.det_ne n)) (AfP p) (S.mx h)).unop := ⟨_, rfl⟩
  choose y hy using fun i k => T.Φ_surj (X i k)
  choose y' hy' using fun i k => T.Φ_surj (X' i k)
  obtain ⟨Y, hYd⟩ : ∃ Y : Matrix (Fin n) (Fin n) (Af E), Y = Matrix.of y := ⟨_, rfl⟩
  obtain ⟨Y', hYd'⟩ : ∃ Y' : Matrix (Fin n) (Fin n) (Af E), Y' = Matrix.of y' := ⟨_, rfl⟩
  have hY : Y.map T.Φ = X := by
    ext i k
    rw [hYd]
    exact hy i k
  have hY' : Y'.map T.Φ = X' := by
    ext i k
    rw [hYd']
    exact hy' i k
  have hXX : X * X' = 1 := by rw [hXd, hXd', ← map_mul, mx_inv, map_one]
  have hXX' : X' * X = 1 := by rw [hXd, hXd', ← map_mul, mx_inv', map_one]
  have hXXs : X * Xs = ((c : AfP p) ⊗ₜ[ℚ] (1 : E)) • (1 : Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E)) := by
    rw [hXd, hXsd, ← map_mul, mx_mem, ← hc]
    ext i k
    rw [hμ]
    rcases eq_or_ne i k with rfl | hik
    · simp
    · simp [Matrix.one_apply, hik]
  have hXsX : Xs * X = ((c : AfP p) ⊗ₜ[ℚ] (1 : E)) • (1 : Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E)) := by
    have h1 : Xs = ((c : AfP p) ⊗ₜ[ℚ] (1 : E)) • X' := by
      calc Xs = (X' * X) * Xs := by rw [hXX', one_mul]
        _ = X' * (X * Xs) := mul_assoc _ _ _
        _ = _ := by rw [hXXs, Matrix.mul_smul, mul_one]
    rw [h1, Matrix.smul_mul, hXX']
  have hMS := hM (AfP p) E A n μ hμ (S.mx h)
  rw [← hXsd, ← hXd] at hMS
  obtain ⟨D, hDd⟩ : ∃ D : Matrix (Fin n) (Fin n) (Af E), D = Matrix.diagonal (fun i => algebraMap E (Af E) (A.dg n i : E)) := ⟨_, rfl⟩
  have hDT : D.map T.Φ = Matrix.diagonal (fun i => (1 : AfP p) ⊗ₜ[ℚ] (A.dg n i : E)) := by
    rw [hDd, Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    exact T.Φ_E _
  have hΦt : T.Φ (finiteAdeleMap ℚ E s0) = (c : AfP p) ⊗ₜ[ℚ] (1 : E) := by rw [T.Φ_Q, hs0]
  have hX : ((Y.map T.Φ).map (conjT E (AfP p)))ᵀ * D.map T.Φ * Y.map T.Φ =
      T.Φ (finiteAdeleMap ℚ E s0) • D.map T.Φ := by
    rw [hY, hDT, hΦt, ← hMS, mul_assoc, hXsX, Matrix.mul_smul, mul_one]
  have hD : (a.val.map (conjFin (conjE E)))ᵀ * D * a.val = 1 := by rw [hDd]; exact ha.1
  have hA : a.val * (a⁻¹).val = 1 := Units.mul_inv a
  have hA' : (a⁻¹).val * a.val = 1 := Units.inv_mul a
  have hGG := inv_part T.Φ heps hker hA hA' (Y := Y) (Y' := Y') (by rw [hY, hY', hXX])
  have hGG' := inv_part T.Φ heps hker hA hA' (Y := Y') (Y' := Y) (by rw [hY, hY', hXX'])
  have hStar := star_part T.Φ (conjFin (conjE E)) (conjT E (AfP p)) (t := finiteAdeleMap ℚ E s0) T.Φ_conj heps hσe hker hA hA' hD hX
  have hConj := conj_part T.Φ hΦe hA hA' (Y := Y)
  have h01 : (1 - e) * (s0 * s1 - 1) = 0 := hkerQ _ (by rw [map_sub, map_mul, hs0, hs1, map_one, Units.mul_inv, sub_self])
  have hss : ((1 - e) * s0 + e) * ((1 - e) * s1 + e) = 1 := by
    linear_combination h01 + (s0 * s1 - s0 - s1 + 1) * heeQ
  have hss' : ((1 - e) * s1 + e) * ((1 - e) * s0 + e) = 1 := by rw [mul_comm]; exact hss
  have hmem : (((⟨_, _, hGG, hGG'⟩ : GL (Fin n) (Af E)), (⟨_, _, hss, hss'⟩ : AfQˣ)) : GL (Fin n) (Af E) × AfQˣ) ∈ GUf E n := by
    refine UpperTheory.Gal.CertificateRingHomMap.mem_Sim.2 ?_
    refine hStar.trans ?_
    congr 1
    simp only [map_add (f := _), map_mul, map_sub, map_one, ← hε]
  refine ⟨⟨_, hmem⟩, ?_, ?_⟩
  · rw [← hXd, ← hY]
    exact hConj.symm
  · intro w hw
    apply Units.ext
    refine Matrix.ext fun i k => ?_
    show pLoc E w (((1 - ε) • ((a⁻¹).val * Y * a.val) + ε • (1 : Matrix (Fin n) (Fin n) (Af E))) i k) = (1 : Matrix (Fin n) (Fin n) _) i k
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _), map_mul, map_sub, map_one, (heE w).1 hw, sub_self, zero_mul,
      zero_add, one_mul]
    rcases eq_or_ne i k with rfl | hik
    · simp
    · simp [Matrix.one_apply, hik]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PAdTEx
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open GlobalTheory.SplitPts (conjE)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap)
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pAdTEx :
    AdQEx → AdTensor → IdemP → AdTEx := by
  intro hQ hT hI p _ E _ _ _
  obtain ⟨Q⟩ := hQ p
  obtain ⟨ι, h1, h2, h3⟩ := hT E
  obtain ⟨e, he, he'⟩ := hI p E
  let M : AfQ ⊗[ℚ] E →ₐ[ℚ] AfP p ⊗[ℚ] E :=
    Algebra.TensorProduct.map Q.ρ.toRatAlgHom (AlgHom.id ℚ E)
  have hM : ∀ (a : AfQ) (x : E), M (a ⊗ₜ x) = Q.ρ a ⊗ₜ x := fun a x => rfl
  have hρe : Q.ρ e = 0 := (Q.ker e).2 fun v hv => (he v).2 hv
  have hιa : ∀ a : AfQ, ι (a ⊗ₜ 1) = finiteAdeleMap ℚ E a := fun a => by
    rw [h1, map_one, mul_one]
  have hιE : ∀ x : E, ι (1 ⊗ₜ x) = algebraMap E (Af E) x := fun x => by
    rw [h1, map_one, one_mul]

  have hMker : ∀ y, M y = 0 → (e ⊗ₜ[ℚ] (1 : E)) * y = y := by
    intro y hy
    let b := Module.finBasis ℚ E
    obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_right b y
    have hc0 : (c.mapRange Q.ρ (map_zero _)).sum (fun i m => m ⊗ₜ[ℚ] b i) = 0 := by
      rw [Finsupp.sum_mapRange_index (by simp)]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hy, Finsupp.sum, Finsupp.sum, map_sum]
      rfl
    have hc := TensorProduct.sum_tmul_basis_right_eq_zero b _ hc0
    have hci : ∀ i, e * c i = c i := by
      intro i
      have hi : Q.ρ (c i) = 0 := by
        have := DFunLike.congr_fun hc i
        simpa using this
      have hv := (Q.ker (c i)).1 hi
      refine Subtype.ext (funext fun v => ?_)
      by_cases hp : (p : 𝓞 ℚ) ∈ v.asIdeal
      · show e v * c i v = c i v
        rw [(he v).1 hp, one_mul]
      · show e v * c i v = c i v
        rw [hv v hp, mul_zero]
    rw [Finsupp.sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hci]

  have hιe : ι (e ⊗ₜ 1) = finiteAdeleMap ℚ E e := hιa e
  have hMe : M (e ⊗ₜ 1) = 0 := by rw [hM, hρe, TensorProduct.zero_tmul]
  have hMker' : ∀ x : Af E, M (ι.symm x) = 0 ↔
      ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → pLoc E w x = 0 := by
    intro x
    constructor
    · intro h w hw
      have h' := congrArg ι (hMker _ h)
      rw [map_mul, hιe, ι.apply_symm_apply] at h'
      rw [← h', map_mul, (he' w).2 hw, zero_mul]
    · intro h
      have hx : finiteAdeleMap ℚ E e * x = x := by
        refine GlobalTheory.EulerTw.pLoc_ext E fun w => ?_
        by_cases hp : (p : 𝓞 E) ∈ w.asIdeal
        · rw [map_mul, (he' w).1 hp, one_mul]
        · rw [map_mul, (he' w).2 hp, zero_mul, h w hp]
      rw [← hx, ← hιe, map_mul ι.symm, ι.symm_apply_apply, map_mul, hMe, zero_mul]
  have hgen : ∀ (a : AfP p) (c : 𝓞 E), IsIntAf a →
      ∃ y ∈ AddSubgroup.closure {y : AfQ ⊗[ℚ] E | ∃ (a : AfQ) (x : 𝓞 E),
        (∀ v : Plc ℚ, Valued.v (a v) ≤ 1) ∧ y = a ⊗ₜ (x : E)}, M y = a ⊗ₜ (c : E) := by
    intro a c ha
    obtain ⟨b, rfl⟩ := Q.surj a
    have hb := (Q.int b).1 ha
    refine ⟨((1 - e) * b) ⊗ₜ (c : E), AddSubgroup.subset_closure ⟨_, c, ?_, rfl⟩, ?_⟩
    · intro v
      by_cases hp : (p : 𝓞 ℚ) ∈ v.asIdeal
      · have : ((1 - e) * b) v = (1 - e v) * b v := rfl
        rw [this, (he v).1 hp, sub_self, zero_mul, map_zero]
        exact zero_le
      · have : ((1 - e) * b) v = (1 - e v) * b v := rfl
        rw [this, (he v).2 hp, sub_zero, one_mul]
        exact hb v hp
    · rw [hM, map_mul, map_sub, map_one, hρe, sub_zero, one_mul]
  have hMs : Function.Surjective M := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a x =>
      obtain ⟨b, rfl⟩ := Q.surj a
      exact ⟨b ⊗ₜ x, rfl⟩
    | add u v hu hv =>
      obtain ⟨u', rfl⟩ := hu
      obtain ⟨v', rfl⟩ := hv
      exact ⟨u' + v', map_add _ _ _⟩
  have hO : ∀ z ∈ OHat p E, ∃ y ∈ AddSubgroup.closure {y : AfQ ⊗[ℚ] E | ∃ (a : AfQ) (x : 𝓞 E),
      (∀ v : Plc ℚ, Valued.v (a v) ≤ 1) ∧ y = a ⊗ₜ (x : E)}, M y = z := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, c, ha, rfl⟩ := hz
      exact hgen a c ha
    | zero => exact ⟨0, zero_mem _, map_zero _⟩
    | add u v _ _ hu hv =>
      obtain ⟨u', hu', rfl⟩ := hu
      obtain ⟨v', hv', rfl⟩ := hv
      exact ⟨u' + v', add_mem hu' hv', map_add _ _ _⟩
    | neg u _ hu =>
      obtain ⟨u', hu', rfl⟩ := hu
      exact ⟨-u', neg_mem hu', map_neg _ _⟩
  have hC : ∀ y ∈ AddSubgroup.closure {y : AfQ ⊗[ℚ] E | ∃ (a : AfQ) (x : 𝓞 E),
      (∀ v : Plc ℚ, Valued.v (a v) ≤ 1) ∧ y = a ⊗ₜ (x : E)}, M y ∈ OHat p E := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, c, ha, rfl⟩ := hy
      exact AddSubgroup.subset_closure ⟨Q.ρ a, c, (Q.int a).2 fun v _ => ha v, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add u v _ _ hu hv => rw [map_add]; exact add_mem hu hv
    | neg u _ hu => rw [map_neg]; exact neg_mem hu
  exact ⟨{ toAdQ := Q
           Φ := (M : AfQ ⊗[ℚ] E →+* AfP p ⊗[ℚ] E).comp (ι.symm : Af E →+* AfQ ⊗[ℚ] E)
           Φ_E := fun x => by
            show M (ι.symm _) = _
            rw [← hιE, ι.symm_apply_apply, hM, map_one]
           Φ_Q := fun a => by
            show M (ι.symm _) = _
            rw [← hιa, ι.symm_apply_apply, hM]
           Φ_surj := fun z => by
            obtain ⟨y, rfl⟩ := hMs z
            refine ⟨ι y, ?_⟩
            show M (ι.symm (ι y)) = _
            rw [ι.symm_apply_apply]
           Φ_ker := hMker'
           Φ_int := fun x => by
            show M (ι.symm x) ∈ OHat p E ↔ _
            constructor
            · intro hx w hw
              obtain ⟨y, hy, hyz⟩ := hO _ hx
              have hd : M (ι.symm (x - ι y)) = 0 := by
                rw [map_sub, map_sub, ι.symm_apply_apply, hyz, sub_self]
              have h0 := (hMker' _).1 hd w hw
              rw [map_sub, sub_eq_zero] at h0
              rw [h0]
              exact (h2 y).1 hy w
            · intro hx
              have hz : M (ι.symm (finiteAdeleMap ℚ E e * x)) = 0 := by
                rw [← hιe, map_mul ι.symm, ι.symm_apply_apply, map_mul, hMe, zero_mul]
              have hi : ι.symm (x - finiteAdeleMap ℚ E e * x) ∈ AddSubgroup.closure
                  {y : AfQ ⊗[ℚ] E | ∃ (a : AfQ) (x : 𝓞 E),
                    (∀ v : Plc ℚ, Valued.v (a v) ≤ 1) ∧ y = a ⊗ₜ (x : E)} := by
                refine (h2 _).2 fun w => ?_
                rw [ι.apply_symm_apply, map_sub, map_mul]
                by_cases hp : (p : 𝓞 E) ∈ w.asIdeal
                · rw [(he' w).1 hp, one_mul, sub_self, map_zero]
                  exact zero_le
                · rw [(he' w).2 hp, zero_mul, sub_zero]
                  exact hx w hp
              have := hC _ hi
              rwa [map_sub, map_sub, hz, sub_zero] at this
           Φ_conj := fun x => by
            show M (ι.symm (conjFin (conjE E) x)) = conjT E (AfP p) (M (ι.symm x))
            obtain ⟨y, rfl⟩ := ι.surjective x
            rw [ι.symm_apply_apply]
            induction y using TensorProduct.inductionOn with
            | tmul a z =>
              rw [h1, map_mul, h3, conjFin_algebraMap, ← h1, ι.symm_apply_apply, hM, hM, conjT_tmul]
              rfl
            | add u v hu hv =>
              simp only [map_add (f := _), hu, hv] }⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PAdQEx
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct

open Rat.HeightOneSpectrum GlobalTheory.NormLevelCompare in
private theorem away_iff (p : ℕ) [hp : Fact p.Prime] (w : HeightOneSpectrum ℤ) :
    w.asIdeal ≠ Ideal.span {(p : ℤ)} ↔ (p : 𝓞 ℚ) ∉ (primeCorr w).asIdeal := by
  have mem : ∀ {R : Type} [CommRing R] [Algebra R ℚ] [IsIntegralClosure R ℤ ℚ]
      (v : HeightOneSpectrum R) (n : ℕ), (n : R) ∈ v.asIdeal ↔ natGenerator v ∣ n := by
    intro R _ _ _ v n
    rw [natGenerator_dvd_iff, ← map_natCast (Rat.IsIntegralClosure.intEquiv R) n,
      Ideal.apply_mem_of_equiv_iff]
  have key : primesEquiv (primeCorr w) = primesEquiv w := by
    change primesEquiv (primesEquiv.symm (primesEquiv w)) = _
    exact Equiv.apply_symm_apply _ _
  have hg : natGenerator (primeCorr w) = natGenerator w := congrArg Subtype.val key
  rw [mem, hg, ← mem (R := ℤ)]
  refine not_congr ⟨fun h ↦ h ▸ Ideal.mem_span_singleton_self _, fun h ↦ ?_⟩
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp.out).irreducible
  exact (hmax.eq_of_le w.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 h)).symm

private theorem ringEquiv_of_algEquiv {K A B : Type*} [CommSemiring K] [Semiring A] [Semiring B]
    {_ : Algebra K A} {_ : Algebra K B} (e : A ≃ₐ[K] B) : ∃ f : A ≃+* B, ∀ x, f x = e x := ⟨e.toRingEquiv, fun _ ↦ rfl⟩

open GlobalTheory.NormLevelCompare in
private theorem exists_local_ring (w : HeightOneSpectrum ℤ) :
    ∃ e : (primeCorr w).adicCompletion ℚ ≃+* w.adicCompletion ℚ,
      ∀ x, e x ∈ w.adicCompletionIntegers ℚ ↔ x ∈ (primeCorr w).adicCompletionIntegers ℚ := by
  obtain ⟨e, he⟩ := exists_local w
  obtain ⟨f, hf⟩ := ringEquiv_of_algEquiv e
  exact ⟨f, fun x ↦ by rw [hf]; exact he x⟩

open GlobalTheory.NormLevelCompare in
private noncomputable def eL (w : HeightOneSpectrum ℤ) :
    (primeCorr w).adicCompletion ℚ ≃+* w.adicCompletion ℚ :=
  Classical.choose (exists_local_ring w)

open GlobalTheory.NormLevelCompare in
private theorem eL_mem (w : HeightOneSpectrum ℤ) (x : (primeCorr w).adicCompletion ℚ) :
    eL w x ∈ w.adicCompletionIntegers ℚ ↔ x ∈ (primeCorr w).adicCompletionIntegers ℚ := Classical.choose_spec (exists_local_ring w) x

open GlobalTheory.NormLevelCompare in
private theorem eL_mapsTo (w : HeightOneSpectrum ℤ) :
    Set.MapsTo (eL w).toRingHom ((primeCorr w).adicCompletionIntegers ℚ) (w.adicCompletionIntegers ℚ) := fun x hx ↦ (eL_mem w x).2 hx

private theorem finiteAdeleRingAway_ext {p : ℕ} {x y : AfP p} (h : ∀ v, AfP.eval v x = AfP.eval v y) : x = y := RestrictedProduct.ext _ _ h

open GlobalTheory.NormLevelCompare in
private noncomputable def rho (p : ℕ) : AfQ →+* AfP p :=
  RestrictedProduct.mapAlongRingHom (fun u : HeightOneSpectrum (𝓞 ℚ) ↦ u.adicCompletion ℚ)
    (fun v : AwayP p ↦ v.1.adicCompletion ℚ)
    (B₁ := fun u ↦ u.adicCompletionIntegers ℚ) (B₂ := fun v ↦ v.1.adicCompletionIntegers ℚ)
    (fun v ↦ primeCorr v.1) (primeCorr.injective.comp Subtype.val_injective).tendsto_cofinite
    (fun v ↦ (eL v.1).toRingHom) (hφ := .of_forall fun v ↦ eL_mapsTo v.1)

open GlobalTheory.NormLevelCompare in
private theorem eval_rho {p : ℕ} (a : AfQ) (v : AwayP p) :
    AfP.eval v (rho p a) = eL v.1 (a (primeCorr v.1)) := rfl

section
open GlobalTheory.NormLevelCompare
open scoped Classical in
private noncomputable def gL {p : ℕ} (b : AfP p) (w : HeightOneSpectrum ℤ) :
    (primeCorr w).adicCompletion ℚ :=
  if h : w.asIdeal ≠ Ideal.span {(p : ℤ)} then (eL w).symm (AfP.eval (⟨w, h⟩ : AwayP p) b) else 0

private theorem gL_pos {p : ℕ} (b : AfP p) (v : AwayP p) : gL b v.1 = (eL v.1).symm (AfP.eval v b) := by
  unfold gL
  rw [dite_eq_left v.2]
  rfl

private theorem gL_neg {p : ℕ} (b : AfP p) (w : HeightOneSpectrum ℤ)
    (h : ¬ w.asIdeal ≠ Ideal.span {(p : ℤ)}) : gL b w = 0 := by
  unfold gL
  rw [dite_eq_right h]

private theorem afP_ev {p : ℕ} (b : AfP p) :
    ∀ᶠ v : AwayP p in Filter.cofinite, AfP.eval v b ∈ v.1.adicCompletionIntegers ℚ := b.2

private theorem gL_ev {p : ℕ} (b : AfP p) : ∀ᶠ w : HeightOneSpectrum ℤ in Filter.cofinite,
    gL b w ∈ (primeCorr w).adicCompletionIntegers ℚ := by
  have hb := afP_ev b
  rw [Filter.eventually_cofinite] at hb ⊢
  refine (hb.image Subtype.val).subset ?_
  intro w hw
  by_cases h : w.asIdeal ≠ Ideal.span {(p : ℤ)}
  · refine ⟨⟨w, h⟩, ?_, rfl⟩
    intro hv
    apply hw
    rw [show gL b w = _ from gL_pos b ⟨w, h⟩]
    exact (eL_mem w _).1 (by simpa using hv)
  · exact absurd (by rw [gL_neg b w h]; exact zero_mem _) hw

private theorem exists_pi_extend {α β : Type*} (P : β → Type*) (σ : α ≃ β) (g : ∀ a, P (σ a)) :
    ∃ f : ∀ b, P b, ∀ a, f (σ a) = g a := ⟨Equiv.piCongrLeft P σ g, fun a ↦ Equiv.piCongrLeft_apply_apply P σ g a⟩

private noncomputable def fL {p : ℕ} (b : AfP p) : ∀ u : HeightOneSpectrum (𝓞 ℚ), u.adicCompletion ℚ :=
  Classical.choose (exists_pi_extend (fun u : HeightOneSpectrum (𝓞 ℚ) => u.adicCompletion ℚ) primeCorr (gL b))

private theorem fL_corr {p : ℕ} (b : AfP p) (w : HeightOneSpectrum ℤ) : fL b (primeCorr w) = gL b w := Classical.choose_spec
  (exists_pi_extend (fun u : HeightOneSpectrum (𝓞 ℚ) => u.adicCompletion ℚ) primeCorr (gL b)) w

private theorem fL_ev {p : ℕ} (b : AfP p) : ∀ᶠ u : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite,
    fL b u ∈ u.adicCompletionIntegers ℚ := by
  have hg := gL_ev b
  rw [Filter.eventually_cofinite] at hg ⊢
  refine (hg.image primeCorr).subset ?_
  intro u hu
  obtain ⟨w, rfl⟩ := primeCorr.surjective u
  refine ⟨w, ?_, rfl⟩
  intro hw
  apply hu
  rw [fL_corr]
  exact hw

private noncomputable def liftA {p : ℕ} (b : AfP p) : AfQ := ⟨fL b, fL_ev b⟩

private theorem liftA_apply {p : ℕ} (b : AfP p) (u : HeightOneSpectrum (𝓞 ℚ)) : liftA b u = fL b u := rfl

private theorem rho_surj (p : ℕ) : Function.Surjective (rho p) := by
  intro b
  refine ⟨liftA b, finiteAdeleRingAway_ext fun v ↦ ?_⟩
  rw [eval_rho, liftA_apply, fL_corr, gL_pos, RingEquiv.apply_symm_apply]
end

open GlobalTheory.NormLevelCompare in
private theorem rho_ker (p : ℕ) [Fact p.Prime] (a : AfQ) :
    rho p a = 0 ↔ ∀ v : Plc ℚ, (p : 𝓞 ℚ) ∉ v.asIdeal → a v = 0 := by
  constructor
  · intro h v hv
    obtain ⟨w, rfl⟩ := primeCorr.surjective v
    have h2 : eL w (a (primeCorr w)) = 0 :=
      (congrArg (AfP.eval (⟨w, (away_iff p w).2 hv⟩ : AwayP p)) h).trans (map_zero _)
    exact (map_eq_zero_iff _ (eL w).injective).1 h2
  · intro h
    refine finiteAdeleRingAway_ext fun v ↦ ?_
    rw [eval_rho, map_zero, h _ ((away_iff p v.1).1 v.2), map_zero]

open GlobalTheory.NormLevelCompare in
private theorem rho_int (p : ℕ) [Fact p.Prime] (a : AfQ) :
    IsIntAf (rho p a) ↔ ∀ v : Plc ℚ, (p : 𝓞 ℚ) ∉ v.asIdeal → Valued.v (a v) ≤ 1 := by
  constructor
  · intro h v hv
    obtain ⟨w, rfl⟩ := primeCorr.surjective v
    have h2 : eL w (a (primeCorr w)) ∈ w.adicCompletionIntegers ℚ := h ⟨w, (away_iff p w).2 hv⟩
    rw [eL_mem] at h2
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h2
  · intro h v
    show AfP.eval v (rho p a) ∈ _
    rw [eval_rho, eL_mem]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (h _ ((away_iff p v.1).1 v.2))

theorem UpperTheory.Gal.W2.Seed.pAdQEx :
    AdQEx := fun p _ ↦ ⟨⟨rho p, rho_surj p, rho_ker p, rho_int p⟩⟩
end

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKDef
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 Plc comp rat mat)

namespace UpperTheory.Gal.W2.Seed

theorem isoEx'_holds : IsoEx' := fun E _ _ _ A n hn => by
  obtain ⟨a, h1, h2⟩ := UpperTheory.Gal.G1.IsoEx_holds E A n hn
  refine ⟨a, ?_, h2⟩
  rw [Matrix.diagonal_map (map_zero _)] at h1
  exact h1

theorem adTEx_holds : AdTEx := pAdTEx pAdQEx pAdTensor pIdemP

theorem trEx_holds : TrEx := pTrEx adTEx_holds pMuEx isoEx'_holds (pJEx pMuStar) pJEq (pJSurj pIdemP pMuStar)

theorem latCoord_holds : LatCoord := pLatCoord pRepLaws

theorem vecCoord_holds : VecCoord := pVecCoord latCoord_holds pEvEx

end UpperTheory.Gal.W2.Seed

namespace UpperTheory.Gal.Int.Geo.Pl

open UpperTheory.Gal.W2.Seed

theorem intCof_holds : UpperTheory.Gal.Int.Geo.Pl.IntCof := fun E _ _ _ n g => pIntCof E n (mat g)

theorem frameEx_holds : FrameEx := fun E _ _ _ A n p _ S hn => by
  obtain ⟨T⟩ := trEx_holds E A n p S hn
  obtain ⟨vec, v1, v2, v3, v4, v5, v6⟩ := vecCoord_holds E A n p S T
  obtain ⟨B, x, hx, hm, he⟩ := pStdForm2 pMuStar E A n p S T
  exact ⟨{
    j := T.j
    surj := fun h => ⟨T.sec h, T.j_sec h⟩
    ker := fun g => by simpa using T.j_eq g 1
    a := fun w => GeneralLinearGroup.map (pLoc E w) T.a
    a_int := T.iso.2
    a_cof := pIntCof E n T.a
    vec := vec
    vec_inj := v1
    vec_hat := v2
    vec_surj := v3
    vec_in := v4
    vec_act := v5
    vec_mul := v6
    ρ := T.ρ
    ρ_int := T.int
    mult := T.j_sim
    B := B
    x := x
    t := 1
    hx := hx
    mem := hm
    emb1 := he
    emb2 := fun y _ h' => ⟨fun h => (pPInt E A n p S ⟨y, h'⟩ h).1, fun h => pPIntRev pIntConj E A n p S ⟨y, h'⟩ h⟩
    th := CertificateRingHomMap.th
    th_mat := fun _ => rfl
    th_sim := fun _ => rfl
    tr := T
    j_tr := rfl
    a_tr := fun _ => rfl }⟩

end UpperTheory.Gal.Int.Geo.Pl
