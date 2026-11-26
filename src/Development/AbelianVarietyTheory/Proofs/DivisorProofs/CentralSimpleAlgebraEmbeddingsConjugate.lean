module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.TraceDefinitePairsEqAutomorphicTrace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwOrbUEqZeroOfCusp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedLatticeColumnLatticeMulIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockOperatorsLieRepresentationCommute
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualMeasureExistsUniqueFourierInversion

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbKEqZeroOfCusp
noncomputable section

open MeasureTheory Matrix
open scoped Classical

namespace GlobalTheory.OrbDesc

theorem orbK_eq_twOrbU {G : Type} [Group G] (K0 : Subgroup G) (γ : G) (f : G → ℂ)
    (hbi : ∀ k ∈ K0, ∀ k' ∈ K0, ∀ g, f (k * g * k') = f g) :
    GlobalTheory.LKCount.orbK (MonoidHom.id G) K0 γ f =
      GlobalTheory.LKLoc.twOrbU (MonoidHom.id G) K0 γ (GlobalTheory.BCT.twCent (MonoidHom.id G) γ ⊓ K0) f := by
  unfold GlobalTheory.LKCount.orbK GlobalTheory.LKCount.orbC GlobalTheory.LKLoc.twOrbU GlobalTheory.LKLoc.orbSum
  refine finsum_congr fun q => ?_
  have hc : (fun k : K0 => f ((Quotient.out q * k)⁻¹ * γ * (MonoidHom.id G) (Quotient.out q * k))) =
      fun _ => f ((Quotient.out q)⁻¹ * γ * Quotient.out q) := by
    funext k
    have := hbi (k : G)⁻¹ (K0.inv_mem k.2) k k.2 ((Quotient.out q)⁻¹ * γ * Quotient.out q)
    rw [← this]
    simp only [MonoidHom.id_apply, _root_.mul_inv_rev, mul_assoc]
  rw [hc, avg_const']
  simp only [MonoidHom.id_apply, GlobalTheory.LKCount.vol, GlobalTheory.LKLoc.volRat, GlobalTheory.LKLoc.locPart]
  congr 1
  push_cast
  rw [inv_div]

end GlobalTheory.OrbDesc

namespace GlobalTheory.LKCount

theorem orbK_eq_zero_of_cusp : ∀ (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (f : GL ι K → ℂ), IsLocallyConstant f → HasCompactSupport f →
  (∀ (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b), 0 < a → 0 < b → ∀ (μ : Measure (Fin a → Fin b → K)), μ.IsAddHaarMeasure →
    ∀ u : (Fin a → Fin b → K) → GL ι K,
      (∀ X, (u X : Matrix ι ι K) = Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) →
      ∀ g h : GL ι K, ∫ X, f (g * (h⁻¹ * u X * h)) ∂μ = 0) →
  ∀ γ : GL ι K, (γ : Matrix ι ι K).charpoly.Separable → ¬ Irreducible (γ : Matrix ι ι K).charpoly →
  ∀ (K0 : Subgroup (GL ι K)), IsOpen (K0 : Set (GL ι K)) → IsCompact (K0 : Set (GL ι K)) →
    (∀ k ∈ K0, ∀ k' ∈ K0, ∀ g, f (k * g * k') = f g) →
    GlobalTheory.LKCount.orbK (MonoidHom.id (GL ι K)) K0 γ f = 0 := by
  intro K _ _ _ _ _ _ ι _ _ _ f hlc hcs hyp γ hsep hirr K0 hK0o hK0c hbi
  rw [GlobalTheory.OrbDesc.orbK_eq_twOrbU K0 γ f hbi]
  exact GlobalTheory.OrbDesc.twOrbU_eq_zero_of_cusp K ι f hlc hcs hyp γ hsep hirr K0 K0 hK0o hK0c hK0o hK0c hbi

end GlobalTheory.LKCount
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbKEqZeroOfCharpolyNotSeparable
namespace GlobalTheory

theorem orbK_eq_zero_of_charpoly_not_separable (G : Type) [Group G] (k : Type) [Field k] (n : ℕ)
    (π : G →* GL (Fin n) k) (K : Subgroup G) (δ : G) (f : G → ℂ)
    (hf : ∀ g, f g ≠ 0 → ((π g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly.Separable)
    (hδ : ¬ ((π δ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly.Separable) :
    GlobalTheory.LKCount.orbK (MonoidHom.id G) K δ f = 0 := by
  unfold GlobalTheory.LKCount.orbK GlobalTheory.LKCount.orbC
  apply finsum_eq_zero_of_forall_eq_zero
  intro q
  have hz : ∀ x : G, f (x⁻¹ * δ * x) = 0 := by
    intro x
    by_contra h
    apply hδ
    have hs := hf _ h
    have hc : ((π (x⁻¹ * δ * x) : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly
        = ((π δ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).charpoly := by
      rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul,
        Matrix.charpoly_mul_comm, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    rwa [hc] at hs
  simp [hz]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyAlgHomEqMapMinpoly
open scoped TensorProduct

namespace GlobalTheory.CsaCharpoly
open Polynomial

theorem injective_of_isSimpleRing {R S : Type} [Ring R] [IsSimpleRing R] [Ring S] [Nontrivial S]
    (f : R →+* S) : Function.Injective f := by
  rcases eq_bot_or_eq_top (TwoSidedIdeal.ker f) with h | h
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have : x ∈ TwoSidedIdeal.ker f := (TwoSidedIdeal.mem_ker f).2 hx
    rw [h] at this
    simpa using this
  · exfalso
    have : (1 : R) ∈ TwoSidedIdeal.ker f := by rw [h]; trivial
    rw [TwoSidedIdeal.mem_ker, map_one] at this
    exact one_ne_zero this

theorem natDegree_minpoly_le_one_tmul {F A : Type} [Field F] [Ring A] [Algebra F A] (K : Type)
    [Field K] [Algebra F K] (g : A) (hK : IsIntegral K ((1 : K) ⊗ₜ[F] g)) :
    (minpoly F g).natDegree ≤ (minpoly K ((1 : K) ⊗ₜ[F] g)).natDegree := _root_.GlobalTheory.CentSep.natDegree_minpoly_le_baseChange (F := F) (A := A) K g hK

end GlobalTheory.CsaCharpoly

namespace GlobalTheory
open Polynomial

theorem charpoly_algHom_eq_map_minpoly : ∀ (F L C : Type) [Field F] [Field L] [Algebra F L] [Ring C]
    [Algebra F C] [Algebra.IsCentral F C] [IsSimpleRing C] [FiniteDimensional F C] (n : ℕ),
    Module.finrank F C = n ^ 2 → ∀ (ι : C →ₐ[F] Matrix (Fin n) (Fin n) L) (y : C),
    (minpoly F y).natDegree = n → (ι y).charpoly = (minpoly F y).map (algebraMap F L) := by
  intro F L C _ _ _ _ _ _ _ _ n _ ι a hdeg
  have ha : IsIntegral F a := IsIntegral.of_finite F a
  have hn : 0 < n := hdeg ▸ minpoly.natDegree_pos ha
  haveI : NeZero n := ⟨hn.ne'⟩
  let g : L ⊗[F] C →ₐ[L] Matrix (Fin n) (Fin n) L :=
    Algebra.TensorProduct.lift (Algebra.ofId L _) ι (fun l y ↦ Algebra.commute_algebraMap_left l _)
  haveI : IsSimpleRing (L ⊗[F] C) := GroundTheory.Brauer.isSimpleRing_tensorProduct_of_right
  have hg : Function.Injective g := GlobalTheory.CsaCharpoly.injective_of_isSimpleRing g.toRingHom
  have eg : g ((1 : L) ⊗ₜ a) = ι a := by
    simp only [g]; erw [Algebra.TensorProduct.lift_tmul]; simp
  have hyi : IsIntegral L ((1 : L) ⊗ₜ[F] a) := IsIntegral.of_finite L _
  have hxi : IsIntegral L (ι a) := IsIntegral.of_finite L _
  have hmin : minpoly L (ι a) = minpoly L ((1 : L) ⊗ₜ[F] a) := by
    rw [← eg]; exact minpoly.algHom_eq g hg _
  have hge : n ≤ (minpoly L (ι a)).natDegree := by
    rw [hmin, ← hdeg]; exact GlobalTheory.CsaCharpoly.natDegree_minpoly_le_one_tmul L a hyi
  have hdvd : minpoly L (ι a) ∣ (minpoly F a).map (algebraMap F L) := by
    apply minpoly.dvd
    rw [aeval_map_algebraMap, aeval_algHom_apply, minpoly.aeval, map_zero]
  have hmonic : ((minpoly F a).map (algebraMap F L)).Monic := (minpoly.monic ha).map _
  have hdm : ((minpoly F a).map (algebraMap F L)).natDegree = n := by rw [natDegree_map, hdeg]
  have e1 : (minpoly F a).map (algebraMap F L) = minpoly L (ι a) :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hxi) hmonic hdvd (by rw [hdm]; exact hge)
  have e2 : (ι a).charpoly = minpoly L (ι a) :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hxi) (Matrix.charpoly_monic _)
      (Matrix.minpoly_dvd_charpoly _) (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; exact hge)
  rw [e2, e1]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyDvdPowOfAevalEqZero
open Polynomial

namespace GlobalTheory.SepCharpoly

theorem charpoly_dvd_pow_of_aeval_eq_zero {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n R) (p : R[X]) (hp : aeval M p = 0) : M.charpoly ∣ p ^ Fintype.card n := _root_.GlobalTheory.UnitLemma.Centraliser.charpoly_dvd_pow_of_aeval_eq_zero (R := R) (n := n) M p hp

theorem not_separable_charpoly : ∀ (F L C : Type) [Field F] [Field L] [Algebra F L] [Ring C] [Algebra F C]
    [FiniteDimensional F C] (n : ℕ) (ι : C →ₐ[F] Matrix (Fin n) (Fin n) L) (y : C),
    ((minpoly F y).natDegree < n ∨ ((minpoly F y).natDegree = n ∧ ¬ (minpoly F y).Separable)) →
      ¬ (ι y).charpoly.Separable := by
  intro F L C _ _ _ _ _ _ n ι y h hc
  have hyi : IsIntegral F y := IsIntegral.of_finite F y
  have hpm : (minpoly F y).Monic := minpoly.monic hyi
  have h1 : aeval (ι y) ((minpoly F y).map (algebraMap F L)) = 0 := by
    rw [aeval_map_algebraMap, aeval_algHom_apply, minpoly.aeval, map_zero]
  have h2 : minpoly L (ι y) ∣ (minpoly F y).map (algebraMap F L) := minpoly.dvd L _ h1
  have h3 : (ι y).charpoly ∣ (minpoly L (ι y)) ^ Fintype.card (Fin n) :=
    charpoly_dvd_pow_of_aeval_eq_zero _ _ (minpoly.aeval L _)
  have h4 : (ι y).charpoly ∣ minpoly L (ι y) := hc.squarefree.isRadical _ _ h3
  have h5 := h4.trans h2
  have hmm : ((minpoly F y).map (algebraMap F L)).Monic := hpm.map _
  have hdc : (ι y).charpoly.natDegree = n := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hdm : ((minpoly F y).map (algebraMap F L)).natDegree = (minpoly F y).natDegree := natDegree_map _
  rcases h with h | ⟨h, hns⟩
  · have := natDegree_le_of_dvd h5 hmm.ne_zero
    omega
  · have e := eq_of_monic_of_dvd_of_natDegree_le (Matrix.charpoly_monic _) hmm h5 (by omega)
    rw [← e] at hc
    exact hns ((separable_map (algebraMap F L)).mp hc)

end GlobalTheory.SepCharpoly
end

open MeasureTheory Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.VanishNonEll

open GlobalTheory.BCT GlobalTheory.BCT.OrbProd GlobalTheory.LKCount GlobalTheory.LKCount.OrbKProd

section Transport

variable {A B : Type} [Group A] [Group B]

theorem map_twCent_id (e : A ≃* B) (δ : A) :
    (twCent (MonoidHom.id A) δ).map e.toMonoidHom = twCent (MonoidHom.id B) (e δ) := by
  ext b
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨a, ha, rfl⟩
    have ha' : a * δ = δ * a := ha
    show e a * e δ = e δ * e a
    rw [← map_mul, ha', map_mul]
  · intro hb
    have hb' : b * e δ = e δ * b := hb
    refine ⟨e.symm b, ?_, by simp⟩
    show e.symm b * δ = δ * e.symm b
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hb']

theorem map_conj_equiv (e : A ≃* B) (K : Subgroup A) (x : A) :
    (K.map (MulAut.conj x).toMonoidHom).map e.toMonoidHom =
      (K.map e.toMonoidHom).map (MulAut.conj (e x)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext k
  simp [MulAut.conj_apply]

theorem orbK_congr_equiv (e : A ≃* B) (K : Subgroup A) (δ : A) (F : A → ℂ)
    (hinv : ∀ t ∈ twCent (MonoidHom.id B) (e δ), ∀ k ∈ K.map e.toMonoidHom, ∀ x,
      oTerm (MonoidHom.id B) (K.map e.toMonoidHom) (twCent (MonoidHom.id B) (e δ) ⊓ K.map e.toMonoidHom) (e δ)
          (fun z => F (e.symm z)) (t * x * k) =
        oTerm (MonoidHom.id B) (K.map e.toMonoidHom) (twCent (MonoidHom.id B) (e δ) ⊓ K.map e.toMonoidHom) (e δ)
          (fun z => F (e.symm z)) x) :
    orbK (MonoidHom.id A) K δ F = orbK (MonoidHom.id B) (K.map e.toMonoidHom) (e δ) (fun z => F (e.symm z)) := by
  unfold orbK
  rw [orbC_eq, orbC_eq]
  set TB := twCent (MonoidHom.id B) (e δ)
  set KB := K.map e.toMonoidHom
  have hmemT : ∀ a ∈ TB, e.symm a ∈ twCent (MonoidHom.id A) δ := by
    intro a ha
    rw [← show (twCent (MonoidHom.id A) δ).map e.toMonoidHom = TB from map_twCent_id e δ] at ha
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    simpa using ha'
  have hmemK : ∀ b ∈ KB, e.symm b ∈ K := by
    intro b hb
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    simpa using hb'
  have hpt : ∀ x : A, oTerm (MonoidHom.id A) K (twCent (MonoidHom.id A) δ ⊓ K) δ F x =
      oTerm (MonoidHom.id B) KB (TB ⊓ KB) (e δ) (fun z => F (e.symm z)) (e x) := by
    intro x
    unfold oTerm
    congr 1
    · have h1 : TB ⊓ KB = (twCent (MonoidHom.id A) δ ⊓ K).map e.toMonoidHom := by
        rw [Subgroup.map_inf_eq _ _ _ e.injective, map_twCent_id]
      have h2 : TB ⊓ KB.map (MulAut.conj (e x)).toMonoidHom =
          (twCent (MonoidHom.id A) δ ⊓ K.map (MulAut.conj x).toMonoidHom).map e.toMonoidHom := by
        rw [Subgroup.map_inf_eq _ _ _ e.injective, map_twCent_id, map_conj_equiv]
      rw [h1, h2]
      unfold vol
      rw [Subgroup.relIndex_map_map_of_injective _ _ e.injective,
        Subgroup.relIndex_map_map_of_injective _ _ e.injective]
    · simp
  let Φ : DoubleCoset.Quotient (twCent (MonoidHom.id A) δ : Set A) (K : Set A) →
      DoubleCoset.Quotient (TB : Set B) (KB : Set B) := fun q => DoubleCoset.mk TB KB (e (Quotient.out q))
  have hΦ : Function.Bijective Φ := by
    constructor
    · intro q1 q2 h
      obtain ⟨a, ha, b, hb, h'⟩ := (@DoubleCoset.eq _ _ _ _ _ _).mp h
      calc q1 = DoubleCoset.mk _ K (Quotient.out q1) := (DoubleCoset.out_eq' q1).symm
        _ = DoubleCoset.mk _ K (Quotient.out q2) := by
          rw [DoubleCoset.eq]
          refine ⟨e.symm a, hmemT a ha, e.symm b, hmemK b hb, ?_⟩
          apply e.injective
          simp [h']
        _ = q2 := DoubleCoset.out_eq' q2
    · intro p
      refine ⟨DoubleCoset.mk (twCent (MonoidHom.id A) δ) K (e.symm (Quotient.out p)), ?_⟩
      obtain ⟨a, ha, b, hb, h'⟩ := DoubleCoset.mk_out_eq_mul (twCent (MonoidHom.id A) δ) K (e.symm (Quotient.out p))
      show DoubleCoset.mk TB KB (e (Quotient.out (DoubleCoset.mk (twCent (MonoidHom.id A) δ) K (e.symm (Quotient.out p))))) = p
      rw [h']
      conv_rhs => rw [← DoubleCoset.out_eq' p]
      rw [DoubleCoset.eq]
      have ha' : e a ∈ TB := by rw [← show (twCent (MonoidHom.id A) δ).map e.toMonoidHom = TB from map_twCent_id e δ]; exact Subgroup.mem_map_of_mem _ ha
      have hb' : e b ∈ KB := Subgroup.mem_map_of_mem _ hb
      refine ⟨(e a)⁻¹, TB.inv_mem ha', (e b)⁻¹, KB.inv_mem hb', ?_⟩
      simp [mul_assoc]
  have hz : ∀ q : DoubleCoset.Quotient (twCent (MonoidHom.id A) δ : Set A) (K : Set A), oTerm (MonoidHom.id A) K (twCent (MonoidHom.id A) δ ⊓ K) δ F (Quotient.out q) =
      oTerm (MonoidHom.id B) KB (TB ⊓ KB) (e δ) (fun z => F (e.symm z)) (Quotient.out (Equiv.ofBijective Φ hΦ q)) := by
    intro q
    rw [hpt]
    obtain ⟨a, ha, b, hb, h'⟩ := DoubleCoset.mk_out_eq_mul TB KB (e (Quotient.out q))
    show _ = oTerm (MonoidHom.id B) KB (TB ⊓ KB) (e δ) (fun z => F (e.symm z)) (Quotient.out (DoubleCoset.mk TB KB (e (Quotient.out q))))
    rw [h', hinv a ha b hb]
  rw [finsum_congr hz]
  exact finsum_comp_equiv (Equiv.ofBijective Φ hΦ)
    (f := fun q => oTerm (MonoidHom.id B) KB (TB ⊓ KB) (e δ) (fun z => F (e.symm z)) (Quotient.out q))

end Transport

section Prod

variable {G₁ G₂ : Type} [Group G₁] [Group G₂] [TopologicalSpace G₁] [TopologicalSpace G₂]
  [IsTopologicalGroup G₁] [IsTopologicalGroup G₂]

end Prod

theorem natDegree_minpoly_le (F L C : Type) [Field F] [Field L] [Algebra F L] [Ring C]
    [Algebra F C] [Algebra.IsCentral F C] [IsSimpleRing C] [FiniteDimensional F C] (n : ℕ) (hn : 0 < n)
    (ι : C →ₐ[F] Matrix (Fin n) (Fin n) L) (a : C) : (minpoly F a).natDegree ≤ n := by
  haveI : NeZero n := ⟨hn.ne'⟩
  let g : L ⊗[F] C →ₐ[L] Matrix (Fin n) (Fin n) L :=
    Algebra.TensorProduct.lift (Algebra.ofId L _) ι (fun l y ↦ Algebra.commute_algebraMap_left l _)
  haveI : IsSimpleRing (L ⊗[F] C) := GroundTheory.Brauer.isSimpleRing_tensorProduct_of_right
  have hg : Function.Injective g := GlobalTheory.CsaCharpoly.injective_of_isSimpleRing g.toRingHom
  have eg : g ((1 : L) ⊗ₜ a) = ι a := by
    simp only [g]; erw [Algebra.TensorProduct.lift_tmul]; simp
  have hyi : IsIntegral L ((1 : L) ⊗ₜ[F] a) := IsIntegral.of_finite L _
  have hmin : minpoly L (ι a) = minpoly L ((1 : L) ⊗ₜ[F] a) := by
    rw [← eg]; exact minpoly.algHom_eq g hg _
  have h1 := GlobalTheory.CsaCharpoly.natDegree_minpoly_le_one_tmul L a hyi
  rw [← hmin] at h1
  have h2 : (minpoly L (ι a)).natDegree ≤ (ι a).charpoly.natDegree :=
    Polynomial.natDegree_le_of_dvd (Matrix.minpoly_dvd_charpoly _) (Matrix.charpoly_monic _).ne_zero
  rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at h2
  omega

theorem not_irreducible_map {F L : Type} [Field F] [Field L] (φ : F →+* L) (p : Polynomial F) (hp : p.Monic)
    (hirr : ¬ Irreducible p) : ¬ Irreducible (p.map φ) :=
  fun h => hirr (Polynomial.Monic.irreducible_of_irreducible_map φ p hp h)

end GlobalTheory.VanishNonEll
