module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeGaloisLocalWeightsDeRham
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.GoodRCongr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.EtaPiece
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteChosenSet
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsHeckeGaloisQOfIsHeckeGaloisStatement

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TraceOfCharpoly
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.SpanMulMem
noncomputable section

namespace UpperTheory.GalS.Dbl

open Polynomial Matrix

theorem span_mul_mem {R P Γ : Type} [CommRing R] [Ring P] [Algebra R P] [Monoid Γ] (Φ : Γ →* P) {p q : P}
    (hp : p ∈ Submodule.span R (Set.range Φ)) (hq : q ∈ Submodule.span R (Set.range Φ)) :
    p * q ∈ Submodule.span R (Set.range Φ) := by
  have h := Submodule.mul_mem_mul hp hq
  rw [Submodule.span_mul_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩
  exact ⟨a * b, map_mul Φ a b⟩

theorem span_pair {k Γ : Type} [Field k] [Monoid Γ] {a t : ℕ} (ha : 2 ≤ a) (ρ : Γ →* Matrix (Fin a) (Fin a) k)
    (χ : Fin t → Γ →* k) (hχ : Function.Injective χ) (hρ : Submodule.span k (Set.range ρ) = ⊤)
    (M : Matrix (Fin a) (Fin a) k) (v : Fin t → k) :
    (M, v) ∈ Submodule.span k (Set.range (ρ.prod (Pi.monoidHom χ))) := by
  set B := Submodule.span k (Set.range (ρ.prod (Pi.monoidHom χ))) with hB
  have h1 : ∀ N : Matrix (Fin a) (Fin a) k, ∃ w, (N, w) ∈ B := fun N => by
    have hN : N ∈ Submodule.span k (Set.range ρ) := hρ ▸ Submodule.mem_top
    induction hN using Submodule.span_induction with
    | mem _ h => obtain ⟨g, rfl⟩ := h; exact ⟨_, Submodule.subset_span ⟨g, rfl⟩⟩
    | zero => exact ⟨0, B.zero_mem⟩
    | add _ _ _ _ h h' => obtain ⟨w, h⟩ := h; obtain ⟨w', h'⟩ := h'; exact ⟨_, B.add_mem h h'⟩
    | smul c _ _ h => obtain ⟨w, h⟩ := h; exact ⟨_, B.smul_mem c h⟩
  have h2 : ∀ w : Fin t → k, ∃ N, (N, w) ∈ B := fun w => by
    have hli : LinearIndependent k (fun j => (χ j : Γ → k)) := (linearIndependent_monoidHom Γ k).comp χ hχ
    have hw : w ∈ Submodule.span k (Set.range (flip fun j => (χ j : Γ → k))) :=
      (span_flip_eq_top_iff_linearIndependent.2 hli) ▸ Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem _ h => obtain ⟨g, rfl⟩ := h; exact ⟨_, Submodule.subset_span ⟨g, rfl⟩⟩
    | zero => exact ⟨0, B.zero_mem⟩
    | add _ _ _ _ h h' => obtain ⟨w, h⟩ := h; obtain ⟨w', h'⟩ := h'; exact ⟨_, B.add_mem h h'⟩
    | smul c _ _ h => obtain ⟨w, h⟩ := h; exact ⟨_, B.smul_mem c h⟩
  have h3 : ∀ N N' : Matrix (Fin a) (Fin a) k, (N', (0 : Fin t → k)) ∈ B → (N * N', (0 : Fin t → k)) ∈ B := fun N N' h => by
    obtain ⟨w, hw⟩ := h1 N
    simpa using span_mul_mem (R := k) _ hw h
  have h4 : ∀ N N' : Matrix (Fin a) (Fin a) k, (N * N' - N' * N, (0 : Fin t → k)) ∈ B := fun N N' => by
    obtain ⟨w, hw⟩ := h1 N
    obtain ⟨w', hw'⟩ := h1 N'
    have := B.sub_mem (span_mul_mem (R := k) _ hw hw') (span_mul_mem (R := k) _ hw' hw)
    simpa [mul_comm w w'] using this
  haveI : Nontrivial (Fin a) := Fin.nontrivial_iff_two_le.2 ha
  have h5 : ∀ i : Fin a, (single i i (1 : k), (0 : Fin t → k)) ∈ B := fun i => by
    obtain ⟨j, hj⟩ := exists_ne i
    have e := h3 (single i j 1) _ (h4 (single j j 1) (single j i 1))
    rw [single_mul_single_same, single_mul_single_of_ne (h := hj.symm), sub_zero, single_mul_single_same] at e
    simpa using e
  have h6 : ((1 : Matrix (Fin a) (Fin a) k), (0 : Fin t → k)) ∈ B := by
    have := B.sum_mem (t := Finset.univ) fun i _ => h5 i
    rwa [← prod_mk_sum, sum_single_one, Finset.sum_const_zero] at this
  obtain ⟨N, hN⟩ := h2 v
  have := B.add_mem hN (h3 (M - N) 1 h6)
  simpa using this

theorem hankel_zero {K : Type} [Field K] {n d u : ℕ} (h : d + u < n) (A : Matrix (Fin d) (Fin d) K)
    (B : Matrix (Fin u) (Fin u) K) :
    (Matrix.of fun i j : Fin n => 2 * (A ^ ((i : ℕ) + j)).trace + (B ^ ((i : ℕ) + j)).trace).det = 0 := by
  have hm : (A.charpoly * B.charpoly).Monic := A.charpoly_monic.mul B.charpoly_monic
  have hdeg : (A.charpoly * B.charpoly).natDegree = d + u := by
    rw [A.charpoly_monic.natDegree_mul B.charpoly_monic]; simp
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨fun j => (A.charpoly * B.charpoly).coeff j, fun e => ?_, ?_⟩
  · have := congrFun e ⟨d + u, h⟩
    simp only [Pi.zero_apply] at this
    rw [← hdeg, hm.coeff_natDegree] at this
    exact one_ne_zero this
  · funext i
    have key : ∀ {m : ℕ} (C : Matrix (Fin m) (Fin m) K), aeval C (A.charpoly * B.charpoly) = 0 →
        ∑ j : Fin n, (C ^ ((i : ℕ) + j)).trace * (A.charpoly * B.charpoly).coeff j = 0 := fun C hC => by
      rw [aeval_eq_sum_range' (n := n) (by omega), Finset.sum_range] at hC
      have := congrArg (fun Z => (C ^ (i : ℕ) * Z).trace) hC
      simp only [Finset.mul_sum, Matrix.mul_smul, trace_sum, trace_smul, smul_eq_mul, mul_zero, trace_zero, ← pow_add] at this
      simpa [mul_comm] using this
    have hA := key A (by rw [map_mul, Matrix.aeval_self_charpoly, zero_mul])
    have hB := key B (by rw [map_mul, Matrix.aeval_self_charpoly, mul_zero])
    simp only [mulVec, dotProduct, of_apply, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, hA, hB, Pi.zero_apply]
    simp

theorem hankel_ne {k : Type} [Field k] {n : ℕ} (ν : Fin n → k) (hν : Function.Injective ν) :
    (Matrix.of fun i j : Fin n => ∑ c, ν c ^ ((i : ℕ) + j)).det ≠ 0 := by
  have e : (Matrix.of fun i j : Fin n => ∑ c, ν c ^ ((i : ℕ) + j)) = (vandermonde ν)ᵀ * vandermonde ν := by
    ext i j; simp [Matrix.mul_apply, pow_add]
  rw [e, det_mul, det_transpose]
  exact mul_ne_zero (det_vandermonde_ne_zero_iff.2 hν) (det_vandermonde_ne_zero_iff.2 hν)

theorem core {O K k Γ : Type} [CommRing O] [Field K] [Field k] [Monoid Γ] (f : O →+* K) (hf : Function.Injective f)
    (res : O →+* k) (hres : Function.Surjective res) {a t d u : ℕ} (ha : 2 ≤ a) (hdu : d + u < a + t)
    (r : Γ →* Matrix (Fin (a + t)) (Fin (a + t)) O) (σ : Γ →* Matrix (Fin d) (Fin d) K) (υ : Γ →* Matrix (Fin u) (Fin u) K)
    (ρ : Γ →* Matrix (Fin a) (Fin a) k) (χ : Fin t → Γ →* k) (hχ : Function.Injective χ)
    (hρ : Submodule.span k (Set.range ρ) = ⊤)
    (h1 : ∀ g, f (r g).trace = 2 * (σ g).trace + (υ g).trace)
    (h2 : ∀ g, res (r g).trace = (ρ g).trace + ∑ j, χ j g) (ν : Fin (a + t) → k) (hν : Function.Injective ν) : False := by
  letI := f.toAlgebra
  letI := res.toAlgebra
  let Φ := r.prod ((σ.prod υ).prod (ρ.prod (Pi.monoidHom χ)))
  let S := Submodule.span O (Set.range Φ)
  have hS : ∀ p ∈ S, f p.1.trace = 2 * p.2.1.1.trace + p.2.1.2.trace ∧ res p.1.trace = p.2.2.1.trace + ∑ j, p.2.2.2 j := by
    intro p hp
    induction hp using Submodule.span_induction with
    | mem _ h => obtain ⟨g, rfl⟩ := h; exact ⟨h1 g, h2 g⟩
    | zero => simp
    | add _ _ _ _ h h' =>
      simp only [Prod.fst_add, Prod.snd_add, trace_add, map_add (f := _), h.1, h.2, h'.1, h'.2, Pi.add_apply, Finset.sum_add_distrib]
      constructor <;> ring
    | smul c _ _ h =>
      have a1 : ∀ z : K, c • z = f c * z := fun z => Algebra.smul_def c z
      have a2 : ∀ z : k, c • z = res c * z := fun z => Algebra.smul_def c z
      simp only [Prod.smul_fst, Prod.smul_snd, trace_smul, smul_eq_mul, map_mul, h.1, h.2, Pi.smul_apply, a1, a2,
        ← Finset.mul_sum]
      constructor <;> ring
  have hl : ∀ q ∈ Submodule.span k (Set.range (ρ.prod (Pi.monoidHom χ))), ∃ p ∈ S, p.2.2 = q := by
    intro q hq
    induction hq using Submodule.span_induction with
    | mem _ h => obtain ⟨g, rfl⟩ := h; exact ⟨Φ g, Submodule.subset_span ⟨g, rfl⟩, rfl⟩
    | zero => exact ⟨0, S.zero_mem, rfl⟩
    | add _ _ _ _ h h' => obtain ⟨p, hp, rfl⟩ := h; obtain ⟨p', hp', rfl⟩ := h'; exact ⟨_, S.add_mem hp hp', rfl⟩
    | smul c _ _ h =>
      obtain ⟨p, hp, rfl⟩ := h
      obtain ⟨c, rfl⟩ := hres c
      exact ⟨_, S.smul_mem c hp, (algebraMap_smul k c p.2.2).symm⟩
  obtain ⟨p, hp, e⟩ := hl _ (span_pair ha ρ χ hχ hρ (diagonal fun i => ν (Fin.castAdd t i)) fun j => ν (Fin.natAdd a j))
  have hpow : ∀ m : ℕ, p ^ m ∈ S := fun m => by
    induction m with
    | zero => exact Submodule.subset_span ⟨1, by rw [map_one, pow_zero]⟩
    | succ m ih => rw [pow_succ]; exact span_mul_mem Φ ih hp
  let Hm : Matrix (Fin (a + t)) (Fin (a + t)) O := Matrix.of fun i j => (p.1 ^ ((i : ℕ) + j)).trace
  have e1 : f.mapMatrix Hm = Matrix.of fun i j : Fin (a + t) =>
      2 * (p.2.1.1 ^ ((i : ℕ) + j)).trace + (p.2.1.2 ^ ((i : ℕ) + j)).trace := by
    ext i j; exact (hS _ (hpow _)).1
  have e2 : res.mapMatrix Hm = Matrix.of fun i j : Fin (a + t) => ∑ c, ν c ^ ((i : ℕ) + j) := by
    ext i j
    have := (hS _ (hpow ((i : ℕ) + j))).2
    simp only [Prod.pow_snd, Prod.pow_fst, e, diagonal_pow, trace_diagonal, Pi.pow_apply] at this
    rw [of_apply, Fin.sum_univ_add]
    exact this
  have z : Hm.det = 0 := hf (by rw [RingHom.map_det, e1, hankel_zero hdu, map_zero])
  exact hankel_ne ν hν (by rw [← e2, ← RingHom.map_det, z, map_zero])

end UpperTheory.GalS.Dbl
end
end

noncomputable section

namespace UpperTheory.GalS

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.AbsoluteIrreducibilityOfTraceSpan

theorem cyc_onto (D : D7) (i : D.nd.Loc) (k : Fin 2) (hl : D.nd.l i = D.host.g k) (u : ℤ_[D.nd.l i]ˣ) :
    ∃ g : GE D.nd, cycZ (F := D.host.E) (Ω := D.nd.Om) (D.nd.l i) g = u := by
  haveI : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  obtain ⟨w, hw⟩ := GlobalTheory.OChoose.placesOver_nonempty D.host.E (D.nd.l i) (D.nd.lPrime i).out
  have h1 : (D.nbr i w hw).Kw.1 = ⊥ := IntermediateField.finrank_eq_one_iff.1 ((GlobalTheory.TypeDegOne.degree_one D i k hl).2 w hw)
  obtain ⟨σ, -, hσu⟩ := GlobalTheory.Cyc.exists_inertia_cycZ_eq (D.nd.l i) u
  have hσ : σ ∈ Formalism.BasicNotions.Loc.GK (D.nbr i w hw).Kw := by
    refine GlobalTheory.EpsInertia.mem_GK _ σ fun x => ?_
    have hx := (D.nbr i w hw).j_E x
    rw [h1, IntermediateField.mem_bot] at hx
    obtain ⟨q, hq⟩ := hx
    rw [← hq]; exact σ.commutes q
  refine ⟨((D.nbr i w hw).e.symm ⟨σ, hσ⟩).1, ?_⟩
  rw [GlobalTheory.EpsInertia.cycZ_bridge (D.nbr i w hw), MulEquiv.apply_symm_apply]
  exact hσu

theorem charP_res (D : D7) (i : D.nd.Loc) : CharP (IsLocalRing.ResidueField (D.nd.O i)) (D.nd.l i) := by
  have hm := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := ℤ_[D.nd.l i]) (IsLocalRing.maximalIdeal (D.nd.O i))
  change ((IsLocalRing.maximalIdeal (D.nd.O i)).comap (algebraMap ℤ_[D.nd.l i] (D.nd.O i))).IsMaximal at hm
  have h1 : ((D.nd.l i : ℕ) : ℤ_[D.nd.l i]) ∈ (IsLocalRing.maximalIdeal (D.nd.O i)).comap (algebraMap ℤ_[D.nd.l i] (D.nd.O i)) := by
    rw [IsLocalRing.eq_maximalIdeal hm]
    exact PadicInt.irreducible_p.not_isUnit
  rw [Ideal.mem_comap, map_natCast, ← IsLocalRing.residue_eq_zero_iff, map_natCast] at h1
  exact (CharP.charP_iff_prime_eq_zero (D.nd.lPrime i).out).2 h1

def chiBar (D : D7) (i : D.nd.Loc) (j : Fin D.R.t) : GE D.nd →* IsLocalRing.ResidueField (D.nd.O i) :=
  (IsLocalRing.residue (D.nd.O i)).toMonoidHom.comp ((Units.coeHom _).comp (D.nd.chi i ((j : ℕ) + 1)))

theorem chiBar_inj (D : D7) (i : D.nd.Loc) (k : Fin 2) (hl : D.nd.l i = D.host.g k) : Function.Injective (chiBar D i) := by
  intro j j' e
  haveI := charP_res D i
  have hp : (D.nd.l i).Prime := (D.nd.lPrime i).out
  have hbig : 16 * D.R.t ^ 2 < D.nd.l i := hl ▸ DiscreteGroups.sglob.DzType.big_of_le_nV D k (by unfold Ranks.nV; omega)
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod (D.nd.l i))ˣ)
  rw [Nat.card_eq_fintype_card, ZMod.card_units] at hζ
  have hu : IsUnit (((ζ : ZMod (D.nd.l i)).val : ℕ) : ℤ_[D.nd.l i]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (ZMod.val_coe_unit_coprime ζ).symm
  obtain ⟨g, hg⟩ := cyc_onto D i k hl hu.unit
  let φ : (ZMod (D.nd.l i))ˣ →* (IsLocalRing.ResidueField (D.nd.O i))ˣ :=
    Units.map (ZMod.castHom (dvd_refl _) (IsLocalRing.ResidueField (D.nd.O i))).toMonoidHom
  have hφ : Function.Injective φ := Units.map_injective (RingHom.injective _)
  let R : (D.nd.O i)ˣ →* (IsLocalRing.ResidueField (D.nd.O i))ˣ := Units.map (IsLocalRing.residue (D.nd.O i)).toMonoidHom
  have hy : R (Units.map (algebraMap ℤ_[D.nd.l i] (D.nd.O i)).toMonoidHom hu.unit) = φ ζ := by
    apply Units.ext
    show IsLocalRing.residue _ (algebraMap ℤ_[D.nd.l i] (D.nd.O i) (((ζ : ZMod (D.nd.l i)).val : ℕ) : ℤ_[D.nd.l i])) =
      ZMod.castHom (dvd_refl _) (IsLocalRing.ResidueField (D.nd.O i)) (ζ : ZMod (D.nd.l i))
    rw [map_natCast, map_natCast]
    conv_rhs => rw [← ZMod.natCast_zmod_val (ζ : ZMod (D.nd.l i)), map_natCast]
  have key : ∀ c : Fin D.R.t, R (D.nd.chi i ((c : ℕ) + 1) g) = R (D.nd.chi i 1 g) * (φ ζ ^ (c : ℕ))⁻¹ := fun c => by
    rw [D.nd.chi_def i ((c : ℕ) + 1) (by omega) (by omega), MonoidHom.mul_apply, map_mul, MonoidHom.zpow_apply,
      MonoidHom.comp_apply, hg, map_zpow, hy, ← zpow_natCast, ← zpow_neg]
    congr 2
    push_cast; ring
  have e1 : R (D.nd.chi i ((j : ℕ) + 1) g) = R (D.nd.chi i ((j' : ℕ) + 1) g) := Units.ext (DFunLike.congr_fun e g)
  rw [key, key, mul_right_inj, inv_inj, ← map_pow, ← map_pow] at e1
  have hj := j.2
  have hj' := j'.2
  exact Fin.ext (pow_injOn_Iio_orderOf (by rw [Set.mem_Iio, hζ]; have : D.R.t ≤ D.R.t ^ 2 := Nat.le_self_pow two_ne_zero _; omega)
    (by rw [Set.mem_Iio, hζ]; have : D.R.t ≤ D.R.t ^ 2 := Nat.le_self_pow two_ne_zero _; omega) (hφ e1))

theorem trace_of_charpoly {k : Type} [Field k] {a t : ℕ} (M : Matrix (Fin (a + t)) (Fin (a + t)) k) (A : Matrix (Fin a) (Fin a) k)
    (c : Fin t → k) (h : M.charpoly = A.charpoly * ∏ j, (X - C (c j))) : M.trace = A.trace + ∑ j, c j := by
  have e : M.charpoly = (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 (Matrix.diagonal c))).charpoly := by
    rw [h, Matrix.charpoly_reindex, Matrix.charpoly_fromBlocks_zero₁₂, Matrix.charpoly_diagonal]
  rw [Matrix.trace_eq_neg_charpoly_nextCoeff, e, ← Matrix.trace_eq_neg_charpoly_nextCoeff]
  simp [Matrix.trace, Fin.sum_univ_add]

theorem trace_sumRep {k Γ : Type} [CommRing k] [Group Γ] {a b : ℕ} (ρ : Γ →* GL (Fin a) k) (ρ' : Γ →* GL (Fin b) k) (g : Γ) :
    ((SumRepresentations.At.sumRep ρ ρ' g : GL (Fin (a + b)) k) : Matrix (Fin (a + b)) (Fin (a + b)) k).trace =
      (ρ g : Matrix (Fin a) (Fin a) k).trace + (ρ' g : Matrix (Fin b) (Fin b) k).trace := by
  have e : ((SumRepresentations.At.sumRep ρ ρ' g : GL (Fin (a + b)) k) : Matrix (Fin (a + b)) (Fin (a + b)) k) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (ρ g : Matrix (Fin a) (Fin a) k) 0 0 (ρ' g : Matrix (Fin b) (Fin b) k)) := rfl
  rw [e]
  simp [Matrix.trace, Fin.sum_univ_add]

theorem noDouble_of_live (D : D7) (h5 : SumRepresentations.adm5 D) (i : D.nd.Loc) (k : Fin 2) (hl : D.nd.l i = D.host.g k)
    (hL : GlobalTheory.CoefDuty.Live D.nd i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (hr : GoodR D.nd i r)
    (hb : ResidualCharpolyIndependent D.nd i r) (x : D.nd.X i) {K' : Type} [Field K'] (f : D.nd.O i →+* K') (hf : Function.Injective f) {d u : ℕ}
    (σ : GE D.nd →* GL (Fin d) K') (υ : GE D.nd →* GL (Fin u) K') (h : d + d + u = D.R.nV) (Pm : GL (Fin D.R.nV) K')
    (hd : 0 < d)
    (hrel : ∀ g, ((Pm⁻¹ * mapRep f (r x) g * Pm : GL (Fin D.R.nV) K') : Matrix (Fin D.R.nV) (Fin D.R.nV) K') =
      Matrix.reindex (finCongr h) (finCongr h) ((SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ g : GL (Fin (d + d + u)) K') :
        Matrix (Fin (d + d + u)) (Fin (d + d + u)) K')) : False := by
  classical
  obtain ⟨π, -, r0, ρ0, hr0, ⟨e0, he0⟩, habs⟩ := hL
  haveI := charP_res D i
  have hbig : 16 * D.R.nV ^ 2 < D.nd.l i := hl ▸ DiscreteGroups.sglob.DzType.big_of_le_nV D k le_rfl
  have hn : D.R.nV = D.R.r + D.R.t := rfl
  have hr2 : 2 ≤ D.R.r := by have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  refine Dbl.core f hf (IsLocalRing.residue (D.nd.O i)) IsLocalRing.residue_surjective (a := D.R.r) (t := D.R.t) hr2
    (d := d) (u := u) (by omega) ((Units.coeHom _).comp (r x)) ((Units.coeHom _).comp σ) ((Units.coeHom _).comp υ)
    ((Units.coeHom _).comp (mapRep (IsLocalRing.residue (D.nd.O i)) ρ0)) (chiBar D i) (chiBar_inj D i k hl)
    (GlobalTheory.BurnsideField.span_mat_eq_top_of_absIrrSub _ habs) (fun g => ?_) (fun g => ?_) (fun c => ((c : ℕ) : _)) fun c c' e => ?_
  · have t := congrArg Matrix.trace (hrel g)
    rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul] at t
    have t2 : (Matrix.reindex (finCongr h) (finCongr h) ((SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ g : GL (Fin (d + d + u)) K') :
        Matrix (Fin (d + d + u)) (Fin (d + d + u)) K')).trace = ((SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ g : GL (Fin (d + d + u)) K') :
        Matrix (Fin (d + d + u)) (Fin (d + d + u)) K').trace :=
      Equiv.sum_comp (finCongr h).symm fun j => ((SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ g : GL (Fin (d + d + u)) K') :
        Matrix (Fin (d + d + u)) (Fin (d + d + u)) K') j j
    rw [t2, trace_sumRep, trace_sumRep, ← two_mul] at t
    exact (map_sum f _ _).trans t
  · have d0 := charpoly_of_decomp D i (fun _ => r0) (fun _ => ρ0) π ⟨e0, he0⟩ g
    have hc := charpoly_eq_of_isHeckeGalois GlobalTheory.Published.cheb_holds D i r hr π r0 hr0 g
    have e0' : (mat r0 g).charpoly = (mat ρ0 g).charpoly *
      ∏ c ∈ Finset.Icc 1 D.R.t, (X - C ((chiU D.nd i c g : (D.nd.O i)ˣ) : D.nd.O i)) := d0
    have e1 : ((mat (r x) g).map (IsLocalRing.residue (D.nd.O i))).charpoly =
        ((mat (r π) g).map (IsLocalRing.residue (D.nd.O i))).charpoly := hb x π g
    have e2 : ((mat (r x) g).map (IsLocalRing.residue (D.nd.O i))).charpoly =
        ((mat ρ0 g).map (IsLocalRing.residue (D.nd.O i))).charpoly * ∏ j : Fin D.R.t, (X - C (chiBar D i j g)) := by
      rw [e1, Matrix.charpoly_map, hc, e0', Polynomial.map_mul, ← Matrix.charpoly_map, Polynomial.map_prod]
      congr 1
      rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel, Finset.prod_range]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [Polynomial.map_sub, map_X, map_C, add_comm 1]
      rfl
    exact (map_sum (IsLocalRing.residue (D.nd.O i)) _ _).trans (trace_of_charpoly (a := D.R.r) (t := D.R.t) _ _ _ e2)
  · have h1 := c.2
    have h2 := c'.2
    have h3 : D.R.nV ≤ D.R.nV ^ 2 := Nat.le_self_pow two_ne_zero _
    exact Fin.ext (CharP.natCast_injOn_Iio (IsLocalRing.ResidueField (D.nd.O i)) (D.nd.l i)
      (by rw [Set.mem_Iio]; omega) (by rw [Set.mem_Iio]; omega) e)

end UpperTheory.GalS
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace UpperTheory.GalS.Parts

open UpperTheory.GalS GlobalTheory.NRows GlobalTheory.AbsIrrConstituents Pointwise

theorem placesOver_finite (D : D7) (i : D.nd.Loc) : (placesOver D.host.E (D.nd.l i)).Finite := by
  have hne : Ideal.span {((D.nd.l i : ℕ) : 𝓞 D.host.E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : (D.nd.l i).Prime).ne_zero
  refine (Ideal.finite_factors hne).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.mpr hv

theorem isoLoc_perm (D : D7) {Pa Pa' : List (Part D.naut.CG)} (h : Pa.Perm Pa') (w : PlE D.host) :
    isoLoc D.nd D.naut Pa w = isoLoc D.nd D.naut Pa' w := by
  unfold isoLoc
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [List.foldr_cons, List.map_cons] at ih ⊢; rw [ih]
  | swap x y l =>
    simp only [List.foldr_cons, List.map_cons]
    rw [← D.naut.lpSum_assoc, ← D.naut.lpSum_assoc, D.naut.lpSum_comm (spehLoc _ _ y w)]
  | trans _ _ a b => exact a.trans b

def large₂ (D : D7) : Prop := ∀ (i : D.nd.Loc) (x : D.nd.X i) (P : D.naut.AV i) (Pa : List (Part D.naut.CG)), D.naut.ptV i P = some x → IsBCV D.nd D.naut i P Pa → ∀ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i)), SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ → (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → RelW D.nd D.naut (D.naut.wdOf i ρ w) (D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2))) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), Nc D.nd D.naut (isoLoc D.nd D.naut Pa w) → D.naut.IsdRW i ρ w ∧ UpperTheory.GalN.RelA D.nd D.naut (D.naut.wdOf i ρ w) (D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2)) ∧ ∀ τ, InducesW D.nd i τ w → D.naut.jumpsW i ρ τ = D.naut.locAutHodgeTateWeightsLevelZero i τ

theorem iso_unr (D : D7) (i : D.nd.Loc) (P : D.naut.AV i) (Pa) (w) (hB : IsBCV D.nd D.naut i P Pa) (hQ : w ∉ D.nd.Q i)
    (hg : ∀ k, w ∉ placesOver D.host.E (D.host.g k))
    (hp : w ∉ placesOver D.host.E (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde)) :
    D.naut.unr (isoLoc D.nd D.naut Pa w) := by
  by_cases hs : IsSplitPl D.host w
  · rw [hB.2.2.2.1 w hs]
    exact D.naut.locV_unr i P w hs hQ hg hp
  · exact (hB.2.2.2.2.1 w hs).1

theorem iso_unr_l (D : D7) (i : D.nd.Loc) (P : D.naut.AV i) (Pa) (w) (hB : IsBCV D.nd D.naut i P Pa)
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (hl0 : D.nd.l i ≠ D.host.g 0) (hl1 : D.nd.l i ≠ D.host.g 1) :
    D.naut.unr (isoLoc D.nd D.naut Pa w) := by
  have hl : (D.nd.l i).Prime := Fact.out
  refine iso_unr D i P Pa w hB (fun hq => D.nd.SQ_l i w (Or.inr hq) hw) (fun k => ?_) ?_
  · have hk : D.nd.l i ≠ D.host.g k := by
      fin_cases k
      · exact hl0
      · exact hl1
    exact SumRepresentations.not_over_of_ne hl (D.host.g_prime k) hk hw
  · split_ifs with hpd
    · exact SumRepresentations.not_over_of_ne hl D.host.pde'_prime (hpd ▸ D.host.pde_ne) hw
    · exact SumRepresentations.not_over_of_ne hl D.host.pde_prime hpd hw

theorem point_determines : ∀ D : D7, SumRepresentations.adm1 D → SumRepresentations.adm5 D → (∀ (i : D.nd.Loc) (x : D.nd.X i), ∃ ρ, SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ) → (∀ (i : D.nd.Loc) (x : D.nd.X i) (P : D.naut.AV i) (Pa : List (Part D.naut.CG)), D.naut.ptV i P = some x → IsBCV D.nd D.naut i P Pa → ∀ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i)), SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ → (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → RelW D.nd D.naut (D.naut.wdOf i ρ w) (D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2))) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), Nc D.nd D.naut (isoLoc D.nd D.naut Pa w) → D.naut.IsdRW i ρ w ∧ UpperTheory.GalN.RelA D.nd D.naut (D.naut.wdOf i ρ w) (D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2)) ∧ ∀ τ, InducesW D.nd i τ w → D.naut.jumpsW i ρ τ = D.naut.locAutHodgeTateWeightsLevelZero i τ) → ∀ (i : D.nd.Loc) (P P' : D.naut.AV i), D.naut.ptV i P ≠ none → D.naut.ptV i P = D.naut.ptV i P' → (∀ Pa Pa', IsBCV D.nd D.naut i P Pa → IsBCV D.nd D.naut i P' Pa' → Pa.Perm Pa') ∧ ∀ w, w ∉ D.nd.S i → w ∉ D.nd.Q i → (IsSplitPl D.host w → D.naut.locV i P w = D.naut.locV i P' w) ∧ (¬ IsSplitPl D.host w → ubc D.R.nV (D.naut.satV i P w) = ubc D.R.nV (D.naut.satV i P' w)) := by
  intro D h1 h5 hex hcomp i P P' hP hPP'
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hP
  obtain ⟨ρ, hρ⟩ := hex i x
  have hx' : D.naut.ptV i P' = some x := hPP' ▸ hx
  have perm : ∀ Pa Pa', IsBCV D.nd D.naut i P Pa → IsBCV D.nd D.naut i P' Pa' → Pa.Perm Pa' := by
    intro Pa Pa' hB hB'
    refine h5.2.1 Pa Pa' hB.1 hB'.1 ?_
    filter_upwards [(placesOver_finite D i).compl_mem_cofinite, GlobalTheory.SplitDetermines.isoLoc_unr_ae D.nd D.naut Pa,
      GlobalTheory.SplitDetermines.isoLoc_unr_ae D.nd D.naut Pa'] with w hw u u'
    show isoLoc D.nd D.naut Pa w = isoLoc D.nd D.naut Pa' w
    have e := (((hcomp i x P Pa hx hB ρ hρ).1 w hw).eq_of_unr ((D.naut.unr_tw _ _).2 u)).symm.trans
      (((hcomp i x P' Pa' hx' hB' ρ hρ).1 w hw).eq_of_unr ((D.naut.unr_tw _ _).2 u'))
    have e2 := congrArg (fun a => D.naut.lpTw a (-((1 - (D.R.nV : ℝ)) / 2))) e
    simpa only [D.naut.lpTw_add, add_neg_cancel, D.naut.lpTw_zero] using e2
  have key : ∀ Pa Pa', IsBCV D.nd D.naut i P Pa → IsBCV D.nd D.naut i P' Pa' →
      ∀ w, isoLoc D.nd D.naut Pa w = isoLoc D.nd D.naut Pa' w :=
    fun Pa Pa' hB hB' w => isoLoc_perm D (perm Pa Pa' hB hB') w
  refine ⟨perm, fun w _ _ => ?_⟩
  · obtain ⟨Pa, hB⟩ := h1 i P
    obtain ⟨Pa', hB'⟩ := h1 i P'
    refine ⟨fun hs => ?_, fun hs => ?_⟩
    · rw [← hB.2.2.2.1 w hs, ← hB'.2.2.2.1 w hs, key Pa Pa' hB hB' w]
    · rw [← (hB.2.2.2.2.1 w hs).2, ← (hB'.2.2.2.2.1 w hs).2, key Pa Pa' hB hB' w]

theorem crys_unram_of_lgc (D : D7) (htie : SumRepresentations.tie0 D) (hadm : SumRepresentations.adm1 D) (hLGC : large₂ D) (i : D.nd.Loc)
    (r : D.nd.X i → (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i)))
    (hr : ∀ x, SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x (mapRep (iotaOQ D.nd D.naut i) (r x))) :
    G2a D.nd D.naut i r ∧
    ∀ x w, w ∉ placesOver D.host.E (D.nd.l i) → w ∉ D.nd.S i → w ∉ D.nd.Q i → UnramAt (F := D.host.E) (r x) w := by
  obtain ⟨-, -, hGal⟩ := htie
  have key : ∀ x, ∃ P Pa, D.naut.ptV i P = some x ∧ IsBCV D.nd D.naut i P Pa := fun x => by
    obtain ⟨P, hP⟩ := D.naut.pt_surj i x
    obtain ⟨Pa, hPa⟩ := hadm i P
    exact ⟨P, Pa, hP, hPa⟩
  have hunr := iso_unr D i
  refine ⟨fun w hw hl0 hl1 x => ?_, fun x w hwl hwS hwQ => ?_⟩
  · obtain ⟨P, Pa, hP, hB⟩ := key x
    have hu := iso_unr_l D i P Pa w hB hw hl0 hl1
    have h := (hLGC i x P Pa hP hB _ (hr x)).2 w hw (Nc.of_unr hu)
    exact ⟨(hGal.1 i _ _ w hw (hr x).1).2 ⟨h.1, h.2.1.unr ((D.naut.unr_tw _ _).2 hu)⟩, fun τ hτ => h.2.2 τ hτ⟩
  · obtain ⟨P, Pa, hP, hB⟩ := key x
    have h := (hLGC i x P Pa hP hB _ (hr x)).1 w hwl
    have hS : ¬ ((w ∈ placesOver D.host.E (D.host.g 0) ∨ w ∈ placesOver D.host.E (D.host.g 1) ∨
        w ∈ placesOver D.host.E (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde)) ∧
        w ∉ placesOver D.host.E (D.nd.l i)) := fun hh => hwS ((D.nd.S_def i w).2 hh)
    have hu : D.naut.unr (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (r x)) w) := by
      refine h.unr ?_
      rw [D.naut.unr_tw]
      refine hunr P Pa w hB hwQ (fun k hk => hS ⟨?_, hwl⟩) (fun hk => hS ⟨Or.inr (Or.inr hk), hwl⟩)
      fin_cases k
      · exact Or.inl hk
      · exact Or.inr (Or.inl hk)
    have h1 := (D.naut.wdOf_unr i _ w hwl (hr x).1).1 hu
    intro A hA σ hσ
    obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (D.nd.plOm.2 w) hA
    have hσ' : σ ∈ Ine (F := D.host.E) (g • D.nd.plOm.1 w) := by rw [hg]; exact hσ
    have h2 := h1 _ (ine_conj_of_smul hσ')
    have h3 : mapRep (iotaOQ D.nd D.naut i) (r x) σ = 1 := by
      have e : σ = g * (g⁻¹ * σ * g) * g⁻¹ := by group
      rw [e, map_mul, map_mul, h2, mul_one, ← map_mul, mul_inv_cancel, map_one]
    apply Units.ext
    have h4 := congrArg (fun u : GL (Fin D.R.nV) (Qbar (D.nd.l i)) => u.val) h3
    simp only [mapRep, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, Units.val_one] at h4
    refine Matrix.map_injective (SumRepresentations.iotaOQ_injective D.nd D.naut i) ?_
    show (r x σ).val.map (iotaOQ D.nd D.naut i) = (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).map (iotaOQ D.nd D.naut i)
    rw [Matrix.map_one _ (map_zero _) (map_one _)]
    exact h4

theorem constituentCondition_of_noRepeatedFactor (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i)))
    (hr : ∀ x, SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x (mapRep (iotaOQ D.nd D.naut i) (r x)))
    (hN : ∀ x (K' : Type) [Field K'] (f : D.nd.O i →+* K') (f' : K' →+* Qbar (D.nd.l i)), f'.comp f = iotaOQ D.nd D.naut i →
      ∀ (d u : ℕ) (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin d) K') (υ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin u) K')
        (h : d + d + u = D.R.nV) (Pm : GL (Fin D.R.nV) K'), 0 < d →
        (∀ g, ((Pm⁻¹ * mapRep f (r x) g * Pm : GL (Fin D.R.nV) K') : Matrix (Fin D.R.nV) (Fin D.R.nV) K') =
          Matrix.reindex (finCongr h) (finCongr h) ((SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ g : GL (Fin (d + d + u)) K') :
            Matrix (Fin (d + d + u)) (Fin (d + d + u)) K')) → False) : DistinctAbsIrredConstituents D.nd i r := by
  classical
  letI alg : Algebra (Kf D.nd i) (Qbar (D.nd.l i)) := (D.naut.iotaQ i).toAlgebra
  have hss : ∀ x, IsSSRep (mapRep (algebraMap (Kf D.nd i) (AlgebraicClosure (Kf D.nd i)))
      (mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) (r x))) := by
    intro x
    let f : AlgebraicClosure (Kf D.nd i) →ₐ[Kf D.nd i] Qbar (D.nd.l i) := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    letI : Algebra (AlgebraicClosure (Kf D.nd i)) (Qbar (D.nd.l i)) := f.toRingHom.toAlgebra
    apply SumRepresentations.isSSRep_descent (L := Qbar (D.nd.l i))
    have e : ((algebraMap (AlgebraicClosure (Kf D.nd i)) (Qbar (D.nd.l i))).comp
        (algebraMap (Kf D.nd i) (AlgebraicClosure (Kf D.nd i)))).comp (algebraMap (D.nd.O i) (Kf D.nd i)) =
        iotaOQ D.nd D.naut i := by
      ext z
      show f (algebraMap (Kf D.nd i) _ (algebraMap _ (Kf D.nd i) z)) = D.naut.iotaQ i (algebraMap _ _ z)
      rw [f.commutes]; rfl
    rw [← mapRep_comp, ← mapRep_comp, e]
    exact (hr x).2.1
  obtain ⟨K', hF, hA, hFD, hsplit⟩ :=
    GlobalTheory.T.exists_finiteDimensional_ext_irrSub_absIrr (fun x => mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) (r x)) hss
  refine ⟨K', hF, hA, hFD, fun x => ⟨?_, ?_⟩⟩
  · rw [mapRep_comp]; exact hsplit x
  · intro W₁ W₂ h1 h2 hdis hiso
    let f' : K' →ₐ[Kf D.nd i] Qbar (D.nd.l i) := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    have e' : (f'.toRingHom).comp ((algebraMap (Kf D.nd i) K').comp (algebraMap (D.nd.O i) (Kf D.nd i))) =
        iotaOQ D.nd D.naut i := by
      ext z
      show f' (algebraMap (Kf D.nd i) K' (algebraMap _ (Kf D.nd i) z)) = D.naut.iotaQ i (algebraMap _ _ z)
      rw [f'.commutes]; rfl
    have hQ : mapRep f'.toRingHom (mapRep ((algebraMap (Kf D.nd i) K').comp (algebraMap (D.nd.O i) (Kf D.nd i))) (r x)) =
        mapRep (iotaOQ D.nd D.naut i) (r x) := by
      rw [← mapRep_comp, e']
    have hssK : IsSSRep (mapRep ((algebraMap (Kf D.nd i) K').comp (algebraMap (D.nd.O i) (Kf D.nd i))) (r x)) := by
      letI : Algebra K' (Qbar (D.nd.l i)) := f'.toRingHom.toAlgebra
      apply SumRepresentations.isSSRep_descent (L := Qbar (D.nd.l i))
      show IsSSRep (mapRep f'.toRingHom _)
      rw [hQ]; exact (hr x).2.1
    obtain ⟨d, u, σ, υ, h, Pm, hd, hrel⟩ := GlobalTheory.T.exists_conj_double_block_of_iso_subspaces _ W₁ W₂ hssK h1.2.1 h2.2.1 h1.1 hdis hiso
    exact hN x K' _ f'.toRingHom e' d u σ υ h Pm hd hrel

theorem constituentCondition_of_hodgeJumps (D : D7) (ht : SumRepresentations.tie0 D) (i : D.nd.Loc)
    (r : D.nd.X i → (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i))) (hg : GoodR D.nd i r)
    (hon : ∀ x, ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i (mapRep (iotaOQ D.nd D.naut i) (r x)) w ∧
      ∀ τ, InducesW D.nd i τ w → D.naut.jumpsW i (mapRep (iotaOQ D.nd D.naut i) (r x)) τ = D.naut.locAutHodgeTateWeightsLevelZero i τ) :
    DistinctAbsIrredConstituents D.nd i r := by
  have hr := fun x => GlobalTheory.T.isHeckeGaloisQ_of_isHeckeGalois' D i x (r x) (hg x)
  refine constituentCondition_of_noRepeatedFactor D i r hr fun x K' _ f f' e' d u σ υ h Pm hd hrel => ?_
  have hQ : mapRep f' (mapRep f (r x)) = mapRep (iotaOQ D.nd D.naut i) (r x) := by rw [← mapRep_comp, e']
  have hrelQ := rel_map' f' h _ σ υ Pm hrel
  rw [hQ] at hrelQ
  have hcQ : SumRepresentations.At.ContQ D.nd i (mapRep (iotaOQ D.nd D.naut i) (r x)) := (hr x).1
  obtain ⟨hcA, hcυ⟩ := continuous_blocks' _ _ _ h _ hrelQ hcQ
  have hcσ : SumRepresentations.At.ContQ D.nd i (mapRep f' σ) :=
    (continuous_blocks' (SumRepresentations.At.sumRep (mapRep f' σ) (mapRep f' σ)) (mapRep f' σ) (mapRep f' σ) rfl 1 (fun g => by simp) hcA).1
  obtain ⟨P, hP⟩ := D.naut.pt_surj i x
  obtain ⟨τ, w, hτw⟩ := GlobalTheory.T.exists_padicAlgCl_embedding_and_place_norm_lt_one D.host.E (D.nd.l i)
  have hpl : ∀ w', InducesW D.nd i τ w' → w' ∈ placesOver D.host.E (D.nd.l i) :=
    fun w' hw' => mem_of_induces' D.host.E (D.nd.l i) τ w' hw'
  have hτ : InducesW D.nd i τ w := hτw
  have hJ := (hon x w (hpl w hτ)).2 τ hτ
  refine jumps_not_nodup' D ht i τ w (hpl w hτ) hτ hpl h _ _ _ _ hd hcQ hcσ hcυ hrelQ
    (fun w' hw' => (hon x w' (hpl w' hw')).1) ?_
  rw [hJ]; exact fixedJumps_nodup D i P τ

theorem constituentCondition_at_distinguishedPrime (D : D7) (h5 : SumRepresentations.adm5 D) (i : D.nd.Loc) (k : Fin 2) (hl : D.nd.l i = D.host.g k)
    (hL : GlobalTheory.CoefDuty.Live D.nd i) (r : D.nd.X i → (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i)))
    (hg : GoodR D.nd i r) (hb : ResidualCharpolyIndependent D.nd i r) : DistinctAbsIrredConstituents D.nd i r :=
  constituentCondition_of_noRepeatedFactor D i r (fun x => GlobalTheory.T.isHeckeGaloisQ_of_isHeckeGalois' D i x (r x) (hg x)) fun x _ _ f f' e' _ _ σ υ h Pm hd hrel =>
    noDouble_of_live D h5 i k hl hL r hg hb x f (by
      have := SumRepresentations.iotaOQ_injective D.nd D.naut i
      rw [← e'] at this
      exact Function.Injective.of_comp (f := f') this) σ υ h Pm hd hrel

theorem lgc (D : D7) (t0 : SumRepresentations.tie0 D) (a2 : AutomorphicGaloisAdmissible D.nd D.naut) (a5 : SumRepresentations.adm5 D) : large₂ D := by
  intro i x P Pa hP hPa ρ hρ
  obtain ⟨ρ0, hc, hs, hw, hl⟩ := isoRep D t0 a2 i P Pa hPa
  obtain ⟨Pm, hPm⟩ := GlobalTheory.T.heckeGaloisRepQbar_conjugate_unique D a5 i x ρ0 ρ (heckeQ D i x P Pa hP hPa ρ0 hc hs hw) hρ
  obtain ⟨c1, c2, c3⟩ := (t0.2.2.2.2.2 i).2.1 _ ρ0 ρ hc Pm hPm
  refine ⟨fun w h => by rw [c2 w (Or.inl h)]; exact hw w h, fun w h hn => ⟨(c1 w h).2 (hl w h hn).1,
    by rw [c2 w (Or.inr (hl w h hn).1)]; exact (hl w h hn).2.1, fun τ hτ => ?_⟩⟩
  rw [c3 τ, (hl w h hn).2.2 τ hτ]
  intro w' hw'
  rw [ind_unique hτ hw']
  exact (hl _ h hn).1

def HeckeGaloisFamilyProperties (D : D7) : Prop := ∀ i : D.nd.Loc,
  ((∃ rq : D.nd.X i → (G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i))), ∀ x, SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x (rq x)) ∧
    ∃ r, GoodR D.nd i r) ∧
  (∀ P P' : D.naut.AV i, D.naut.ptV i P ≠ none → D.naut.ptV i P = D.naut.ptV i P' →
    (∀ Pa Pa', IsBCV D.nd D.naut i P Pa → IsBCV D.nd D.naut i P' Pa' → Pa.Perm Pa') ∧
    ∀ w, w ∉ D.nd.S i → w ∉ D.nd.Q i →
      (IsSplitPl D.host w → D.naut.locV i P w = D.naut.locV i P' w) ∧
      (¬ IsSplitPl D.host w → ubc D.R.nV (D.naut.satV i P w) = ubc D.R.nV (D.naut.satV i P' w))) ∧
  ∀ r, GoodR D.nd i r → SumRepresentations.At.G1 D.nd i r ∧ G2a D.nd D.naut i r ∧ G3 D.nd i r ∧ SumRepresentations.At.G4 D.nd i r

theorem heckeGaloisFamilyProperties_of_admissible (D : D7) (t0 : SumRepresentations.tie0 D) (hO : SumRepresentations.hypO D) (a1 : SumRepresentations.adm1 D) (a2 : AutomorphicGaloisAdmissible D.nd D.naut) (a5 : SumRepresentations.adm5 D) :
    HeckeGaloisFamilyProperties D := by
  have ex : ∀ (i : D.nd.Loc) (x : D.nd.X i), ∃ ρ, SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ := fun i x => by
    obtain ⟨P, hP⟩ := D.naut.pt_surj i x
    obtain ⟨Pa, hPa⟩ := a1 i P
    obtain ⟨ρ, hc, hs, hw, -⟩ := isoRep D t0 a2 i P Pa hPa
    exact ⟨ρ, heckeQ D i x P Pa hP hPa ρ hc hs hw⟩
  have lg := lgc D t0 a2 a5
  intro i
  have exq : ∃ rq : D.nd.X i → (G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i))),
      ∀ x, SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x (rq x) := ⟨fun x => (ex i x).choose, fun x => (ex i x).choose_spec⟩
  refine ⟨⟨exq, SumRepresentations.exists_GoodR D.nd D.naut hO i exq⟩, point_determines D a1 a5 ex lg i, fun r hr => ?_⟩
  have he := fun x => GlobalTheory.T.isHeckeGaloisQ_of_isHeckeGalois' D i x (r x) (hr x)
  have g1 : SumRepresentations.At.G1 D.nd i r := SumRepresentations.charpoly_clause_of_chebotarev D.nd a5.2.2.1 i r hr
  have gb : ResidualCharpolyIndependent D.nd i r := SumRepresentations.residual_charpoly_of_chebotarev_clause D.nd i r g1
  have cu := crys_unram_of_lgc D t0 a1 lg i r he
  refine ⟨g1, cu.1, ⟨fun hg => ?_, gb⟩, cu.2⟩
  by_cases hl : D.nd.l i ≠ D.host.g 0 ∧ D.nd.l i ≠ D.host.g 1
  · refine constituentCondition_of_hodgeJumps D t0 i r hr fun x w hw => ?_
    obtain ⟨P, hP⟩ := D.naut.pt_surj i x
    obtain ⟨Pa, hPa⟩ := a1 i P
    have h := (lg i x P Pa hP hPa _ (he x)).2 w hw (Nc.of_unr (iso_unr_l D i P Pa w hPa hw hl.1 hl.2))
    exact ⟨h.1, h.2.2⟩
  · have hL := hg.resolve_left hl
    by_cases h0 : D.nd.l i = D.host.g 0
    · exact constituentCondition_at_distinguishedPrime D a5 i 0 h0 hL r hr gb
    · exact constituentCondition_at_distinguishedPrime D a5 i 1 (by by_contra h1; exact hl ⟨h0, h1⟩) hL r hr gb

end UpperTheory.GalS.Parts
