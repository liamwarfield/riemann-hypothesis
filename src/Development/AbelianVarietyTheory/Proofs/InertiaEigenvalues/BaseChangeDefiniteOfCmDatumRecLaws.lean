module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFundamentalDomainMassOneCocompactLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesIdempotentMulOfMapsToParabolicInduction
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerLawUpperTriangularUnipotentAdelic

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeDefiniteOfCmDatumRecLaws
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.DefiniteBC

namespace GlobalTheory.DefiniteBCFrozen

attribute [local instance] GlobalTheory.CuspRep.host_isCMField

theorem isBC_of_isBaseChange {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
    {B : NBC A} {j : ℕ} {π : B.AU j} {Pa : List (Part A.CG)}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.BaseChangeDistinctness.IsBaseChange B j π Pa) : SphericalInertData.IsBC N A B j π Pa := by
  refine ⟨fun p hp => ⟨(h.discrete p hp).1, (h.discrete p hp).2, h.conjSelfDual p hp⟩, ?_, h.rank, h.split,
    h.inert, h.inf⟩
  refine h.distinct.map ?_
  rintro ⟨a, π, d⟩ ⟨a', π', d'⟩ hh
  simp only [Prod.mk.injEq, Sigma.mk.injEq] at hh
  obtain ⟨⟨rfl, h2⟩, rfl⟩ := hh
  cases h2
  rfl

end GlobalTheory.DefiniteBCFrozen

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoLocalAllOfTateDualityEulerChar
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoLocalAllOfTateDualityEulerChar
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.BlochKatoLocalAllOfTateDualityEulerChar₂

theorem aux_of_blochKato_tateDuality_eulerChar₂ :
    GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
      ∀ D : D7, LocalSituation.Conclusion5 D :=
  GlobalTheory.BlochKatoLocalOfHyp.blochKatoLocal_allPrimes_of_blochKato

end GlobalTheory.BlochKatoLocalAllOfTateDualityEulerChar₂
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoLocalAllOfTateDualityEulerCharStatement
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blochKatoLocal_all_of_tateDuality_eulerChar : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ D : D7, LocalSituation.Conclusion5 D := by
  first | exact @GlobalTheory.BlochKatoLocalAllOfTateDualityEulerChar₂.aux_of_blochKato_tateDuality_eulerChar₂ | exact GlobalTheory.BlochKatoLocalAllOfTateDualityEulerChar₂.aux_of_blochKato_tateDuality_eulerChar₂ | (intros; apply GlobalTheory.BlochKatoLocalAllOfTateDualityEulerChar₂.aux_of_blochKato_tateDuality_eulerChar₂ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoAnnihilatorAllOfTateDualityEulerChar
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoAnnihilatorAllOfTateDualityEulerChar
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.BKaRows

theorem bkaAll_of_hypotheses : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK →
    Formalism.GaloisCohomology.LocalEulerCharK → ∀ D : D7, Formalism.MainNotions.N.K.Rows.BKaAll D := by
  intro hBK hTD hEC D i
  exact bloch_kato_annihilator_above_l D i (GlobalTheory.BlochKatoLocalOfHyp.blochKatoLocal_allPrimes_of_blochKato hBK hTD hEC D) GlobalTheory.T.padicIntegers_finiteExt_goodCoefficientRing

end GlobalTheory.BKaRows
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoAnnihilatorAllOfTateDualityEulerCharStatement
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blochKatoAnnihilator_all_of_tateDuality_eulerChar : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ D : D7, Formalism.MainNotions.N.K.Rows.BKaAll D := by
  first | exact @GlobalTheory.BKaRows.bkaAll_of_hypotheses | exact GlobalTheory.BKaRows.bkaAll_of_hypotheses | (intros; apply GlobalTheory.BKaRows.bkaAll_of_hypotheses <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrincipalCongruenceFixedVectorsLeSmoothVectors
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesEqProdOfParabolicInductionChain
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesEqProdOfParabolicInductionChain
open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp GlobalTheory.SerSys GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders
open scoped Classical

namespace GlobalTheory.SerSys

theorem has_prod_of_inInd : ∀ (g : ℕ) [Fact g.Prime] (S : Sys g) (π : GLRep g) (L : List (GLRep g)), InInd π L → ∀ F, Has S π.2.ρ F → ∃ fs : List (ZMod g)[X], List.Forall₂ (fun (ρ : GLRep g) f => Has S ρ.2.ρ f) L fs ∧ F = fs.prod := by
  intro g _ S π L hL
  induction hL with
  | nil π h0 _ =>
    intro F hF
    refine ⟨[], List.Forall₂.nil, ?_⟩
    obtain ⟨n, r⟩ := π
    simp only at h0
    subst h0
    obtain ⟨v, -, hv⟩ := hF
    have hne : S.e 0 F ≠ 0 := by
      intro h
      apply hv
      simp [h, actK]
    obtain ⟨hm, hd, -⟩ := S.label 0 F hne
    simpa using Polynomial.eq_one_of_monic_natDegree_zero hm hd
  | cons π σ ρ L hπ _ _ hmap ih =>
    intro F hF
    obtain ⟨f, f', hf, hf', rfl⟩ :=
      GlobalTheory.T.seriesIdempotent_mul_of_maps_to_parabolicInduction g S π.1 σ.1 ρ.1 _ π.2.ρ _ _ σ.2.ρ ρ.2.ρ hπ hmap F hF
    obtain ⟨fs, hfs, rfl⟩ := ih f hf
    exact ⟨f' :: fs, List.Forall₂.cons hf' hfs, by simp [mul_comm]⟩

end GlobalTheory.SerSys
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesEqProdOfParabolicInductionChainStatement
open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp GlobalTheory.SerSys GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.series_eq_prod_of_parabolic_induction_chain : ∀ (g : ℕ) [Fact g.Prime] (S : Sys g) (π : GLRep g) (L : List (GLRep g)), InInd π L → ∀ F, Has S π.2.ρ F → ∃ fs : List (ZMod g)[X], List.Forall₂ (fun (ρ : GLRep g) f => Has S ρ.2.ρ f) L fs ∧ F = fs.prod := by
  first | exact @GlobalTheory.SerSys.has_prod_of_inInd | exact GlobalTheory.SerSys.has_prod_of_inInd | (intros; apply GlobalTheory.SerSys.has_prod_of_inInd <;> assumption)
end
end

noncomputable section

namespace GlobalTheory.SerSys.TameGen

open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp CategoryTheory
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

def IsSC (ρ : GLRep g) : Prop := 0 < ρ.1 ∧ IsIrrRep ρ.2.ρ ∧ PRep.IsSupercuspidal ρ.2.ρ

def Inflates {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) ℚ_[g]) V)
    (τ : FDRep ℂ (Gn g n)) : Prop :=
  ∃ φ : τ →ₗ[ℂ] V, φ ≠ 0 ∧ ∀ (k : GL (Fin n) ℤ_[g]) (w : τ), φ (τ.ρ (red g n k) w) = π (inc g n k) (φ w)

def liftPoly (teich : Formalism.CyclotomicNorms.Fbar g → ℂ) (f : (ZMod g)[X]) : ℂ[X] :=
  ((Formalism.CyclotomicNorms.rootsBar f).map fun x => X - C (teich x)).prod

def SupportCompat {LP : Type} (ine : LP → ℂ[X]) (rec : GLRep g → LP) : Prop :=
  ∀ π : GLRep g, IsIrrRep π.2.ρ → PRep.IsSmooth π.2.ρ →
    ∃ L : List (GLRep g), InInd π L ∧ (∀ ρ ∈ L, IsSC ρ) ∧ ine (rec π) = (L.map fun ρ => ine (rec ρ)).prod

def DepthZeroCuspidal (g : ℕ) [Fact g.Prime] : Prop :=
  ∀ ρ : GLRep g, IsSC ρ → fixK1 ρ.2.ρ ≠ ⊥ → FiniteGL.IsCuspidal (repK ρ.2.ρ)

theorem liftPoly_one (teich : Formalism.CyclotomicNorms.Fbar g → ℂ) : liftPoly teich (1 : (ZMod g)[X]) = 1 := by
  simp [liftPoly, Formalism.CyclotomicNorms.rootsBar]

theorem liftPoly_mul (teich : Formalism.CyclotomicNorms.Fbar g → ℂ) {f f' : (ZMod g)[X]} (hf : f ≠ 0) (hf' : f' ≠ 0) :
    liftPoly teich (f * f') = liftPoly teich f * liftPoly teich f' := by
  unfold liftPoly Formalism.CyclotomicNorms.rootsBar
  rw [Polynomial.map_mul, roots_mul (mul_ne_zero (map_ne_zero hf) (map_ne_zero hf')), Multiset.map_add (f := _),
    Multiset.prod_add]

theorem Has.monic {S : Sys g} {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin n) ℚ_[g]) V} {f : (ZMod g)[X]} (h : Has S π f) : f.Monic := by
  obtain ⟨v, -, hv⟩ := h
  refine (S.label n f fun e => hv ?_).1
  simp [e, actK]

theorem exists_simple {G W : Type} [Group G] [Fintype G] [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W)
    (e : MonoidAlgebra ℂ G) (he : ∀ a, e * a = a * e) (w : W) (hw : w ≠ 0) (hew : σ.asAlgebraHom e w = w) :
    ∃ (τ : FDRep ℂ G) (φ : τ →ₗ[ℂ] W), Simple τ ∧ Function.Injective φ ∧ (∀ x u, φ (τ.ρ x u) = σ x (φ u)) ∧
      Representation.asAlgebraHom τ.ρ e = 1 := by
  let P : Submodule ℂ W → Prop := fun U => U ≠ ⊥ ∧ FiniteDimensional ℂ U ∧ (∀ x, ∀ u ∈ U, σ x u ∈ U) ∧
    ∀ u ∈ U, σ.asAlgebraHom e u = u
  have hex : ∃ m, ∃ U, P U ∧ Module.finrank ℂ U = m := by
    refine ⟨_, Submodule.span ℂ (Set.range fun x => σ x w), ⟨?_, ?_, ?_, ?_⟩, rfl⟩
    · intro h
      exact hw (by simpa using (Submodule.span_eq_bot.1 h) _ ⟨1, rfl⟩)
    · exact FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
    · intro x u hu
      refine (show _ ≤ Submodule.comap (σ x) (Submodule.span ℂ (Set.range fun x => σ x w)) from
        Submodule.span_le.2 ?_) hu
      rintro _ ⟨y, rfl⟩
      exact Submodule.subset_span ⟨x * y, by simp⟩
    · intro u hu
      refine (show _ ≤ LinearMap.eqLocus (σ.asAlgebraHom e) LinearMap.id from Submodule.span_le.2 ?_) hu
      rintro _ ⟨y, rfl⟩
      show σ.asAlgebraHom e (σ y w) = σ y w
      rw [← Representation.asAlgebraHom_single_one, ← Module.End.mul_apply, ← map_mul, he, map_mul,
        Module.End.mul_apply, hew]
  obtain ⟨U, ⟨h0, hfin, hst, hfix⟩, hm⟩ := Nat.find_spec hex
  have hmin : ∀ U', P U' → Module.finrank ℂ U ≤ Module.finrank ℂ U' := fun U' h =>
    hm ▸ Nat.find_min' hex ⟨U', h, rfl⟩
  let σU : Representation ℂ G U := PRep.sub σ U hst
  have hirr : IsIrrRep σU := by
    refine ⟨Submodule.nontrivial_iff_ne_bot.2 h0, fun T hT => or_iff_not_imp_left.2 fun hT0 => ?_⟩
    have hP : P (T.map U.subtype) := by
      refine ⟨fun h => hT0 (Submodule.map_injective_of_injective U.injective_subtype (by simpa using h)), inferInstance, ?_, ?_⟩
      · rintro x _ ⟨u, hu, rfl⟩
        exact ⟨_, hT x u hu, rfl⟩
      · rintro _ ⟨u, -, rfl⟩
        exact hfix _ u.2
    have := hmin _ hP
    rw [Submodule.finrank_map_subtype_eq] at this
    exact Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le T) this)
  refine ⟨FDRep.of σU, U.subtype, ?_, U.injective_subtype, fun _ _ => rfl, ?_⟩
  · have := (Model.isIrrRep_iff σU).1 hirr
    rw [FDRep.simple_iff_char_is_norm_one]
    have hc : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
    have := invertibleOfNonzero hc
    have h := Representation.char_orthonormal σU σU
    rw [if_pos ⟨Representation.Equiv.refl σU⟩, inv_mul_eq_one₀ hc] at h
    exact h.symm
  · refine LinearMap.ext fun u => Subtype.ext ?_
    refine Eq.trans ?_ (hfix _ u.2)
    rw [alg_apply, alg_apply]
    exact (Submodule.coe_sum _ _ _).trans rfl

theorem exists_simple_of_has (S : Sys g) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (f : (ZMod g)[X]) (h : Has S π f) :
    ∃ (τ : FDRep ℂ (Gn g n)) (φ : τ →ₗ[ℂ] fixK1 π), Simple τ ∧ Function.Injective φ ∧
      (∀ x u, φ (τ.ρ x u) = repK π x (φ u)) ∧ Representation.asAlgebraHom τ.ρ (S.e n f) = 1 := by
  obtain ⟨v, hv, hne⟩ := h
  refine exists_simple (repK π) (S.e n f) (S.central n f) ((repK π).asAlgebraHom (S.e n f) ⟨v, hv⟩)
    (fun e => hne ?_) ?_
  · rw [← repK_alg π _ ⟨v, hv⟩, e]; rfl
  · rw [← Module.End.mul_apply, ← map_mul, S.idem]

def LabelsCusp (S : Sys g) (L : LabelDatum g) : Prop :=
  ∀ (d : ℕ) (τ : FDRep ℂ (Gn g d)) (P : (ZMod g)[X]), IsCuspOf L P τ.character →
    Representation.asAlgebraHom τ.ρ (S.e d P) ≠ 0

theorem mem_unipRadical_iff {d a : ℕ} (had : a < d) (x : Gn g d) :
    x ∈ FiniteGL.unipRadical (ZMod g) (FiniteGL.twoBlocks d a) ↔
      InPar a (x : Mt g d) ∧ tl a (x : Mt g d) = ((1 : Gn g a) : Mt g a) ∧
        br a (d - a) (x : Mt g d) = ((1 : Gn g (d - a)) : Mt g (d - a)) := by
  rw [FiniteGL.mem_unipRadical]
  simp only [FiniteGL.twoBlocks, Matrix.sub_apply, sub_eq_zero, Units.val_one]
  constructor
  · intro h
    refine ⟨fun i j hj hi => ?_, ?_, ?_⟩
    · rw [h i j (by simp [hj]), Matrix.one_apply_ne (fun e => by subst e; omega)]
    · ext i j
      have hi : (i : ℕ) < d := by omega
      have hj : (j : ℕ) < d := by omega
      simp only [tl, Formalism.MainNotions.ArithmeticCylinders.entN, hi, hj, and_self, dif_pos]
      rw [h _ _ (by simp)]
      simp [Matrix.one_apply, Fin.ext_iff]
    · ext i j
      have hi : a + (i : ℕ) < d := by omega
      have hj : a + (j : ℕ) < d := by omega
      simp only [br, Formalism.MainNotions.ArithmeticCylinders.entN, hi, hj, and_self, dif_pos]
      rw [h _ _ (by simp)]
      simp [Matrix.one_apply, Fin.ext_iff]
  · rintro ⟨h0, h1, h2⟩ i j hij
    by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a
    · have := congrFun (congrFun h1 ⟨i, hi⟩) ⟨j, hj⟩
      simpa [tl, Formalism.MainNotions.ArithmeticCylinders.entN, Matrix.one_apply, Fin.ext_iff] using this
    · simp [hi, hj] at hij
    · rw [h0 i j hj (by omega), Matrix.one_apply_ne (fun e => by subst e; omega)]
    · have := congrFun (congrFun h2 ⟨i - a, by omega⟩) ⟨j - a, by omega⟩
      have ei : a + (i - a) = i := by omega
      have ej : a + (j - a) = j := by omega
      have e : ((i : ℕ) - a = j - a) ↔ (i : ℕ) = j := by omega
      simpa [br, Formalism.MainNotions.ArithmeticCylinders.entN, Matrix.one_apply, Fin.ext_iff, ei, ej, e] using this

theorem isCusp_character {d : ℕ} (hd : 0 < d) (τ : FDRep ℂ (Gn g d)) (hs : Simple τ)
    (hc : FiniteGL.IsCuspidal τ.ρ) : IsCusp τ.character := by
  refine ⟨hd, ⟨τ, hs, fun _ => rfl⟩, fun a h0 had => ?_⟩
  set U := FiniteGL.unipRadical (ZMod g) (FiniteGL.twoBlocks d a)
  have hz : ∑ u : U, τ.ρ u = 0 := by
    refine LinearMap.ext fun v => (FiniteGL.isCuspidal_iff_twoBlocks τ.ρ).1 hc a h0 had _ fun x hx => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [LinearMap.sum_apply, map_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft (⟨x, hx⟩ : U)) _ _ fun u => ?_
    simp
  have ht := congrArg (LinearMap.trace ℂ τ) hz
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_zero] at ht
  unfold res
  rw [← Finset.sum_filter, Finset.sum_subtype (p := fun x => x ∈ U) _
    (fun x => by rw [mem_unipRadical_iff had]; simp) τ.character]
  exact mul_eq_zero_of_right _ ht

theorem principalCongruenceFixedVectors_le_smoothVectors {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) : fixK1 π ≤ PRep.smoothPart π := by
  intro v hv
  let T : Subgroup (GL (Fin n) ℚ_[g]) :=
    { carrier := {x | π x v = v}
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_ofPred_eq, map_mul, Module.End.mul_apply] at *
        rw [hy, hx]
      one_mem' := by simp
      inv_mem' := by
        intro x hx
        simp only [Set.mem_ofPred_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul]; simp }
  have ho : IsOpen {x : GL (Fin n) ℚ_[g] | ∀ i j, ‖(x.val - 1) i j‖ < 1} := by
    simp only [Set.ofPred_forall]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => isOpen_lt ?_ continuous_const
    exact ((Units.continuous_val.sub continuous_const).matrix_elem i j).norm
  refine T.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset (ho.mem_nhds (by simp)) fun x hx => ?_)
  let N : Matrix (Fin n) (Fin n) ℤ_[g] := Matrix.of fun i j => ⟨(x.val - 1) i j, (hx i j).le⟩
  have hN : (PadicInt.toZMod (p := g)).mapMatrix N = 0 := by
    ext i j
    have : N i j ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by
      rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
      exact hx i j
    exact this
  have hM : (PadicInt.toZMod (p := g)).mapMatrix (N + 1) = 1 := by rw [map_add (f := _), hN, map_one, zero_add]
  have hd : IsUnit (N + 1).det := by
    by_contra h
    have h1 : (N + 1).det ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by
      rw [PadicInt.ker_toZMod]; exact h
    rw [RingHom.mem_ker, RingHom.map_det, hM] at h1
    simp at h1
  let k : GL (Fin n) ℤ_[g] := ((Matrix.isUnit_iff_isUnit_det _).2 hd).unit
  have e1 : red g n k = 1 := Units.ext hM
  have e2 : inc g n k = x := by
    refine Units.ext ?_
    change (algebraMap ℤ_[g] ℚ_[g]).mapMatrix (N + 1) = x.val
    rw [map_add (f := _), map_one]
    exact (congrArg (· + 1) (show (algebraMap ℤ_[g] ℚ_[g]).mapMatrix N = x.val - 1 from rfl)).trans
      (sub_add_cancel _ _)
  exact e2 ▸ (Model.mem_principalCongruenceFixedVectors_iff π v).1 hv k e1

end GlobalTheory.SerSys.TameGen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageMapLatticeEquiv
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageMapLatticeEquiv
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem avg_equiv : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] (G' : Type) [AddCommGroup G'] [TopologicalSpace G'] [IsTopologicalAddGroup G'] [LocallyCompactSpace G'] [SecondCountableTopology G'] [T2Space G'] (Γ : AddSubgroup G) (Γ' : AddSubgroup G'), IsCoLat Γ → IsCoLat Γ' → ∀ e : G ≃ₜ+ G', (∀ x, e x ∈ Γ' ↔ x ∈ Γ) → ∀ Φ : G' → ℂ, Per Γ' Φ → avg Γ (fun x => Φ (e x)) = avg Γ' Φ := by
  intro G _ _ _ _ _ _ G' _ _ _ _ _ _ Γ Γ' hΓ hΓ' e he Φ hΦ
  letI mG : MeasurableSpace G := borel G
  haveI : BorelSpace G := ⟨rfl⟩
  letI mG' : MeasurableSpace G' := borel G'
  haveI : BorelSpace G' := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := GlobalTheory.T.exists_fundamentalDomain_mass_one_cocompactLattice G Γ hΓ
  let f : G ≃ᵐ G' := e.toHomeomorph.toMeasurableEquiv
  haveI := hμ
  have hμ' : (μ.map f).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  let eΓ : Γ' ≃ Γ :=
    { toFun := fun g => ⟨e.symm g, (he _).1 (by simpa using g.2)⟩
      invFun := fun x => ⟨e x, (he x).2 x.2⟩
      left_inv := fun g => Subtype.ext (by simp)
      right_inv := fun x => Subtype.ext (by simp) }
  have hqmp : Measure.QuasiMeasurePreserving f.toEquiv.symm (μ.map f) μ :=
    MeasurePreserving.quasiMeasurePreserving ⟨f.symm.measurable, f.map_symm_map⟩
  have h𝓕' : IsAddFundamentalDomain Γ' (f '' 𝓕) (μ.map f) := by
    refine h𝓕.image_of_equiv f.toEquiv hqmp eΓ fun g x => ?_
    show e (e.symm (g : G') + x) = (g : G') + e x
    rw [map_add (f := _), ContinuousAddEquiv.apply_symm_apply]
  have hm : (μ.map f) (f '' 𝓕) = 1 := by
    rw [MeasurableEquiv.map_apply, Set.preimage_image_eq _ f.injective, h1]
  have hΦ' : Per Γ (fun x => Φ (e x)) :=
    ⟨hΦ.1.comp e.continuous, fun γ hγ x => by show Φ (e (γ + x)) = Φ (e x); rw [map_add (f := _)]; exact hΦ.2 _ ((he γ).2 hγ) _⟩
  have A := (GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average G' Γ' hΓ' (μ.map f) (f '' 𝓕) hμ' h𝓕' Φ hΦ).2.2.2
  have B := (GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average G Γ hΓ μ 𝓕 hμ h𝓕 _ hΦ').2.2.2
  rw [hm] at A
  rw [h1] at B
  simp only [ENNReal.toReal_one, Complex.ofReal_one, one_mul] at A B
  rw [← A, ← B, f.measurableEmbedding.setIntegral_map, Set.preimage_image_eq _ f.injective]
  rfl

end GlobalTheory.CuspGeneric
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageMapLatticeEquivStatement
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotientAverage_map_lattice_equiv : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] (G' : Type) [AddCommGroup G'] [TopologicalSpace G'] [IsTopologicalAddGroup G'] [LocallyCompactSpace G'] [SecondCountableTopology G'] [T2Space G'] (Γ : AddSubgroup G) (Γ' : AddSubgroup G'), IsCoLat Γ → IsCoLat Γ' → ∀ e : G ≃ₜ+ G', (∀ x, e x ∈ Γ' ↔ x ∈ Γ) → ∀ Φ : G' → ℂ, Per Γ' Φ → avg Γ (fun x => Φ (e x)) = avg Γ' Φ := by
  first | exact @GlobalTheory.CuspGeneric.avg_equiv | exact GlobalTheory.CuspGeneric.avg_equiv | (intros; apply GlobalTheory.CuspGeneric.avg_equiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageTranslateInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageTranslateInvariant
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem avg_add_right (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] (Γ : AddSubgroup G) (hΓ : IsCoLat Γ) (Φ : G → ℂ) (hΦ : Per Γ Φ) (y : G) :
    avg Γ (fun x => Φ (x + y)) = avg Γ Φ := by
  letI : MeasurableSpace G := borel G
  haveI : BorelSpace G := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := GlobalTheory.T.exists_fundamentalDomain_mass_one_cocompactLattice G Γ hΓ
  have hΨ : Per Γ (fun x => Φ (x + y)) :=
    ⟨hΦ.1.comp (continuous_add_const y), fun γ hγ x => by simp only [add_assoc, hΦ.2 γ hγ]⟩

  have hpres : MeasurePreserving (fun x : G => x - y) μ μ := by
    simpa [sub_eq_add_neg] using measurePreserving_add_right μ (-y)
  have h𝓕' : IsAddFundamentalDomain Γ ((fun x : G => x - y) ⁻¹' 𝓕) μ :=
    h𝓕.preimage_of_equiv hpres.quasiMeasurePreserving (e := id) Function.bijective_id (fun γ x => by
      simp only [id, AddSubgroup.vadd_def, vadd_eq_add]; abel)
  have hm' : μ ((fun x : G => x - y) ⁻¹' 𝓕) = 1 := by
    rw [hpres.measure_preimage h𝓕.nullMeasurableSet, h1]
  have hA := (GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average G Γ hΓ μ 𝓕 hμ h𝓕 _ hΨ).2.2.2
  have hB := (GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average G Γ hΓ μ _ hμ h𝓕' Φ hΦ).2.2.2
  rw [h1] at hA
  rw [hm'] at hB
  simp only [ENNReal.toReal_one, Complex.ofReal_one, one_mul] at hA hB
  rw [← hA, ← hB]
  have hpres2 : MeasurePreserving (fun x : G => x + y) μ μ := measurePreserving_add_right μ y
  have hemb : MeasurableEmbedding (fun x : G => x + y) := (MeasurableEquiv.addRight y).measurableEmbedding
  have := hpres2.setIntegral_preimage_emb hemb Φ ((fun x : G => x - y) ⁻¹' 𝓕)
  rw [← this]
  have hs : (fun x : G => x + y) ⁻¹' ((fun x : G => x - y) ⁻¹' 𝓕) = 𝓕 := by
    ext x; simp
  rw [hs]

end GlobalTheory.CuspGeneric
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageTranslateInvariantStatement
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotientAverage_translate_invariant : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] (Γ : AddSubgroup G), IsCoLat Γ → ∀ Φ : G → ℂ, Per Γ Φ → ∀ y : G, avg Γ (fun x => Φ (x + y)) = avg Γ Φ := by
  first | exact @GlobalTheory.CuspGeneric.avg_add_right | exact GlobalTheory.CuspGeneric.avg_add_right | (intros; apply GlobalTheory.CuspGeneric.avg_add_right <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalIsometryMapsFlagDomainFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalIsometryMapsFlagDomainFrames
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.FrameDom

open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma emb_cc' (τ : E →+* ℂ) (x : E) : τ (cc x) = conj (τ x) := by
  simp only [ReciprocityTheory.ChartRestriction.G.FD.cc]
  exact IsCMField.complexEmbedding_complexConj E τ x

lemma gram_eq {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G x = xᵀ * G.map τ * x.map (starRingEnd ℂ) := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, ReciprocityTheory.ChartRestriction.G.FD.hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma gm_eq {r : ℕ} (G G' : Matrix (Fin r) (Fin r) E) (γ : Matrix (Fin r) (Fin r) E)
    (h : ∀ v w, herm G (γ.mulVec v) (γ.mulVec w) = herm G' v w) :
    G' = γᵀ * G * γ.map cc := by
  ext i j
  have hij := h (Pi.single i 1) (Pi.single j 1)
  simp only [ReciprocityTheory.ChartRestriction.G.FD.herm, ReciprocityTheory.ChartRestriction.G.FD.cc, Pi.single_apply, map_one, map_zero,
    mul_one, one_mul, mul_zero, zero_mul, ite_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Matrix.mulVec, dotProduct, apply_ite] at hij
  rw [← hij]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul,
    ReciprocityTheory.ChartRestriction.G.FD.cc]
  rw [Finset.sum_comm]

omit [NumberField E] [IsCMField E] in
lemma det_map_ne {r : ℕ} (τ : E →+* ℂ) (γ : GL (Fin r) E) :
    ((γ : Matrix (Fin r) (Fin r) E).map τ).det ≠ 0 := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero τ).2 ((Matrix.isUnit_iff_isUnit_det _).1 γ.isUnit).ne_zero

lemma gram_mul {r : ℕ} (G G' : Matrix (Fin r) (Fin r) E) (γ : Matrix (Fin r) (Fin r) E)
    (h : ∀ v w, herm G (γ.mulVec v) (γ.mulVec w) = herm G' v w) (τ : E →+* ℂ)
    (M : Matrix (Fin r) (Fin r) ℂ) : gram τ G (γ.map τ * M) = gram τ G' M := by
  have h1 : (γ.map τ * M).map (starRingEnd ℂ) = (γ.map cc).map τ * M.map (starRingEnd ℂ) := by
    rw [Matrix.map_mul]
    congr 1
    ext a b
    simp only [Matrix.map_apply, emb_cc']
  have h2 : (γᵀ * G * γ.map cc).map τ = (γ.map τ)ᵀ * G.map τ * (γ.map cc).map τ := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  rw [gram_eq, gram_eq, gm_eq G G' γ h, h2, h1, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

theorem mem_dom_of_isometry :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (γ : GL (Fin r) E), X.p0 = X'.p0 → (∀ τ, τ ∈ X.Ψ ↔ τ ∈ X'.Ψ) → (∀ v w, herm X.Gm ((γ : Matrix (Fin r) (Fin r) E).mulVec v) ((γ : Matrix (Fin r) (Fin r) E).mulVec w) = herm X'.Gm v w) → ∀ (x : Frame X'.Ψ r) (x' : Frame X.Ψ r), x ∈ X'.dom → (∀ (τ : E →+* ℂ) (h₂ : τ ∈ X'.Ψ) (h₁ : τ ∈ X.Ψ), mat x' ⟨τ, h₁⟩ = (γ : Matrix (Fin r) (Fin r) E).map τ * mat x ⟨τ, h₂⟩) → x' ∈ X.dom := by
  intro E _ _ _ r X X' γ hp hΨ hh x x' hx hmat
  simp only [ReciprocityTheory.ChartRestriction.G.FD.Data.dom, ReciprocityTheory.ChartRestriction.G.FD.GG, Set.mem_ofPred_eq] at hx ⊢
  intro τ
  have h₂ : τ.1 ∈ X'.Ψ := (hΨ τ.1).1 τ.2
  obtain ⟨hdet, hpos⟩ := hx ⟨τ.1, h₂⟩
  have hm := hmat τ.1 h₂ τ.2
  refine ⟨?_, fun i => ?_⟩
  · rw [hm, Matrix.det_mul]
    exact mul_ne_zero (det_map_ne τ.1 γ) hdet
  · have hd : dmin X.Gm x' τ i = dmin X'.Gm x ⟨τ.1, h₂⟩ i := by
      simp only [ReciprocityTheory.ChartRestriction.G.FD.dmin]
      rw [hm, gram_mul X.Gm X'.Gm (γ : Matrix (Fin r) (Fin r) E) hh]
    rw [hd, hp]
    exact hpos i

end GlobalTheory.FrameDom
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalIsometryMapsFlagDomainFramesStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalIsometry_maps_flagDomain_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (γ : GL (Fin r) E), X.p0 = X'.p0 → (∀ τ, τ ∈ X.Ψ ↔ τ ∈ X'.Ψ) → (∀ v w, herm X.Gm ((γ : Matrix (Fin r) (Fin r) E).mulVec v) ((γ : Matrix (Fin r) (Fin r) E).mulVec w) = herm X'.Gm v w) → ∀ (x : Frame X'.Ψ r) (x' : Frame X.Ψ r), x ∈ X'.dom → (∀ (τ : E →+* ℂ) (h₂ : τ ∈ X'.Ψ) (h₁ : τ ∈ X.Ψ), mat x' ⟨τ, h₁⟩ = (γ : Matrix (Fin r) (Fin r) E).map τ * mat x ⟨τ, h₂⟩) → x' ∈ X.dom := by
  first | exact @GlobalTheory.FrameDom.mem_dom_of_isometry | exact GlobalTheory.FrameDom.mem_dom_of_isometry | (intros; apply GlobalTheory.FrameDom.mem_dom_of_isometry <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodicEqZeroOfFourierCoefficientsZero
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodicEqZeroOfFourierCoefficientsZero
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

variable {E : Type} [Field E] [NumberField E] {ι : Type} [Fintype ι]

theorem dot_add_right (ξ : ι → E) (x y : ι → Ad E) : dot ξ (x + y) = dot ξ x + dot ξ y := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem dot_add_left (ξ η : ι → E) (x : ι → Ad E) : dot (ξ + η) x = dot ξ x + dot η x := by
  simp only [dot, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem dot_zero_left (x : ι → Ad E) : dot (0 : ι → E) x = 0 := by
  simp [dot]

theorem dot_rat (ξ c : ι → E) :
    dot ξ (fun t => algebraMap E (Ad E) (c t)) = algebraMap E (Ad E) (∑ t, ξ t * c t) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dot, map_sum, map_mul]

theorem dot_single [DecidableEq ι] (t : ι) (c : E) (x : ι → Ad E) :
    dot (Pi.single t c) x = algebraMap E (Ad E) c * x t := by
  rw [dot, Finset.sum_eq_single t]
  · simp
  · intro s _ hs
    simp [Pi.single_eq_of_ne hs]
  · simp

theorem StdPsi.forall_dot_eq_one_iff {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (x : ι → Ad E) :
    (∀ ξ : ι → E, ψ (-dot ξ x) = 1) ↔ x ∈ ratV E ι := by
  classical
  constructor
  · intro h
    have hx : ∀ t, ∃ d : E, x t = algebraMap E (Ad E) d := by
      intro t
      refine hψ.ann _ fun c => ?_
      have h1 := h (Pi.single t c)
      rw [dot_single, AddChar.map_neg_eq_inv, inv_eq_one] at h1
      rwa [mul_comm]
    choose d hd using hx
    exact ⟨d, funext fun t => (hd t).symm⟩
  · rintro ⟨c, rfl⟩ ξ
    have e : (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom ι) c =
        fun t => algebraMap E (Ad E) (c t) := rfl
    rw [e, dot_rat, AddChar.map_neg_eq_inv, hψ.rat, inv_one]

theorem StdPsi.per_twist {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) {Φ : (ι → Ad E) → ℂ} (hΦ : Per (ratV E ι) Φ)
    (ξ : ι → E) : Per (ratV E ι) (fun x => ψ (-dot ξ x) * Φ x) := by
  refine ⟨(hψ.cont.comp (continuous_dot ξ).neg).mul hΦ.1, ?_⟩
  rintro _ ⟨c, rfl⟩ x
  have e : (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom ι) c =
      fun t => algebraMap E (Ad E) (c t) := rfl
  have h2 := hΦ.2 _ ⟨c, rfl⟩ x
  simp only
  rw [h2, AddChar.map_neg_eq_inv, AddChar.map_neg_eq_inv, e, hψ.map_dot ξ c x]

theorem eq_zero_of_avg_character_eq_zero : ∀ (E : Type) [Field E] [NumberField E] (ι : Type) [Fintype ι]
    (ψ : AddChar (Ad E) ℂ), StdPsi ψ → ∀ Φ : (ι → Ad E) → ℂ, Per (ratV E ι) Φ →
    (∀ ξ : ι → E, avg (ratV E ι) (fun x => ψ (-dot ξ x) * Φ x) = 0) → Φ = 0 := by
  intro E _ _ ι _ ψ hψ Φ hΦ hco
  letI : MeasurableSpace (ι → Ad E) := borel _
  haveI : BorelSpace (ι → Ad E) := ⟨rfl⟩
  have hL := isCoLat_ratV E ι
  obtain ⟨hd, K, hK, hcov⟩ := id hL
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := GlobalTheory.T.exists_fundamentalDomain_mass_one_cocompactLattice (ι → Ad E) (ratV E ι) hL
  haveI := hd
  refine GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero (ι → Ad E) (ratV E ι) K hK hcov (ι → E)
    (fun ξ x => ψ (-dot ξ x)) (fun ξ => hψ.cont.comp (continuous_dot ξ).neg) ?_ ?_ ?_
    (fun ξ x => hψ.norm _) (hψ.forall_dot_eq_one_iff) μ 𝓕 hμ h𝓕 Φ hΦ.1 hΦ.2 ?_
  · intro ξ x y
    rw [dot_add_right, neg_add, AddChar.map_add_eq_mul]
  · intro ξ η x
    rw [dot_add_left, neg_add, AddChar.map_add_eq_mul]
  · intro x
    rw [dot_zero_left, neg_zero, AddChar.map_zero_eq_one]
  · intro ξ
    have h2 := (GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average (ι → Ad E) (ratV E ι) hL μ 𝓕 hμ h𝓕 _ (hψ.per_twist hΦ ξ)).2.2.2
    rw [h2, hco ξ, mul_zero]

end GlobalTheory.CuspGeneric
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodicEqZeroOfFourierCoefficientsZeroStatement
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodic_eq_zero_of_fourier_coefficients_zero : ∀ (E : Type) [Field E] [NumberField E] (ι : Type) [Fintype ι] (ψ : AddChar (Ad E) ℂ), StdPsi ψ → ∀ Φ : (ι → Ad E) → ℂ, Per (ratV E ι) Φ → (∀ ξ : ι → E, avg (ratV E ι) (fun x => ψ (-dot ξ x) * Φ x) = 0) → Φ = 0 := by
  first | exact @GlobalTheory.CuspGeneric.eq_zero_of_avg_character_eq_zero | exact GlobalTheory.CuspGeneric.eq_zero_of_avg_character_eq_zero | (intros; apply GlobalTheory.CuspGeneric.eq_zero_of_avg_character_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageAddOfPeriodic
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageAddOfPeriodic
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem avg_add_of_per : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] (Γ : AddSubgroup G), IsCoLat Γ →
    ∀ Φ Φ' : G → ℂ, Per Γ Φ → Per Γ Φ' → avg Γ (fun x => Φ x + Φ' x) = avg Γ Φ + avg Γ Φ' := by
  intro G _ _ _ _ _ _ Γ hΓ Φ Φ' h h'
  letI : MeasurableSpace G := borel G
  haveI : BorelSpace G := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, hF, h1⟩ := GlobalTheory.T.exists_fundamentalDomain_mass_one_cocompactLattice G Γ hΓ
  have hs : Per Γ (fun x => Φ x + Φ' x) :=
    ⟨h.1.add h'.1, fun γ hγ x => by simp only [h.2 γ hγ x, h'.2 γ hγ x]⟩
  obtain ⟨-, -, i1, e1⟩ := GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average G Γ hΓ μ 𝓕 hμ hF Φ h
  obtain ⟨-, -, i2, e2⟩ := GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average G Γ hΓ μ 𝓕 hμ hF Φ' h'
  obtain ⟨-, -, -, e3⟩ := GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average G Γ hΓ μ 𝓕 hμ hF _ hs
  rw [h1] at e1 e2 e3
  simp only [ENNReal.toReal_one, Complex.ofReal_one, one_mul] at e1 e2 e3
  rw [← e1, ← e2, ← e3]
  exact integral_add i1 i2

end GlobalTheory.CuspGeneric
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageAddOfPeriodicStatement
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotientAverage_add_of_periodic : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] (Γ : AddSubgroup G), IsCoLat Γ → ∀ Φ Φ' : G → ℂ, Per Γ Φ → Per Γ Φ' → avg Γ (fun x => Φ x + Φ' x) = avg Γ Φ + avg Γ Φ' := by
  first | exact @GlobalTheory.CuspGeneric.avg_add_of_per | exact GlobalTheory.CuspGeneric.avg_add_of_per | (intros; apply GlobalTheory.CuspGeneric.avg_add_of_per <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fGenerationUnramified
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fGenerationUnramified
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Module

namespace GlobalTheory.GenCountUnram

theorem admGenL_all : ∀ D : D7, Formalism.MainNotions.RamifiedCoefficientChains.H1fGeneratorBoundAll D.loc := by
  intro D l _ K LL
  unfold Formalism.MainNotions.RamifiedCoefficientChains.H1fGeneratorBound
  intro hbij T hT
  have ht := D.locT l
  have hgood := (GlobalTheory.LocalIntegers.good_integers l LL).1
  have h27 := GlobalTheory.T.h1fT_span_card_bound l (D.loc l) (D.locA l) ht K ↥LL.1 ↥(OL LL) hgood T
  have hDR := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l (D.loc l) (D.locA l) ht K LL T.V T.ρ hT).1
  have hgen := h27 hDR
  obtain ⟨s, hs, hcard⟩ := hgen
  let A : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) := ⟨T.V, T.ρ, T.cont⟩
  have hseq0 := GlobalTheory.SeqDim.h1f_finrank l (D.loc l) (D.locA l) ht K ↥LL.1 ↥(OL LL) hgood A
  have hseq := (hseq0 hDR).2
  have hdR0 := GlobalTheory.Per.TiedDdR.ddR_finrank_le l (D.loc l) (D.locA l) ht K LL T.V T.ρ
  haveI := hdR0.1
  have hdR := hdR0.2
  have hK : finrank ℚ_[l] ↥K.1 = finrank ℚ_[l] ↥(K0 K) :=
    (AlgEquiv.ofBijective (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) hbij).toLinearEquiv.finrank_eq.symm
  refine ⟨s, hs, ?_⟩
  rw [hK] at hdR
  have hle : finrank ↥LL.1 ↥(DdR ((D.loc l).PD K) T.ρ ⊓ FilV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V) 0)
      ≤ finrank ↥LL.1 ↥(DdR ((D.loc l).PD K) T.ρ) := Submodule.finrank_mono inf_le_left
  have hmul : finrank ℚ_[l] ↥(K0 K) * finrank ↥LL.1 T.V + finrank ↥LL.1 T.V
      = (finrank ℚ_[l] ↥(K0 K) + 1) * finrank ↥LL.1 T.V := by ring
  rw [← hmul]
  zify at hcard hdR hle ⊢
  linarith

end GlobalTheory.GenCountUnram
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fGenerationUnramifiedStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.h1fGeneratorBoundAll_loc : ∀ D : D7, Formalism.MainNotions.RamifiedCoefficientChains.H1fGeneratorBoundAll D.loc := by
  first | exact @GlobalTheory.GenCountUnram.admGenL_all | exact GlobalTheory.GenCountUnram.admGenL_all | (intros; apply GlobalTheory.GenCountUnram.admGenL_all <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousQuotientAveragePeriodicFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousQuotientAveragePeriodicFamily
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem continuous_avg_of_periodic : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] (Γ : AddSubgroup G), IsCoLat Γ →
    ∀ (X : Type) [TopologicalSpace X] (F : X × G → ℂ), Continuous F →
      (∀ x, ∀ γ ∈ Γ, ∀ y, F (x, γ + y) = F (x, y)) → Continuous fun x => avg Γ (fun y => F (x, y)) := by
  intro G _ _ _ _ _ _ Γ hΓ X _ F hF hper
  letI : MeasurableSpace G := borel G
  haveI : BorelSpace G := ⟨rfl⟩

  obtain ⟨μ, D, hμ, hD, hD1⟩ := GlobalTheory.T.exists_fundamentalDomain_mass_one_cocompactLattice G Γ hΓ
  have hsec : ∀ x : X, Continuous fun y : G => F (x, y) := fun x =>
    hF.comp (continuous_const.prodMk continuous_id)
  have hfacts : ∀ x : X, μ D ≠ 0 ∧ μ D ≠ ⊤ ∧ IntegrableOn (fun y => F (x, y)) D μ ∧
      ∫ y in D, F (x, y) ∂μ = ((μ D).toReal : ℂ) * avg Γ (fun y => F (x, y)) := fun x =>
    GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average G Γ hΓ μ D hμ hD (fun y => F (x, y)) ⟨hsec x, fun γ hγ y => hper x γ hγ y⟩

  have hrepr : (fun x => avg Γ (fun y => F (x, y))) = fun x => ∫ y in D, F (x, y) ∂μ := by
    funext x
    rw [(hfacts x).2.2.2, hD1]
    simp
  rw [hrepr]
  obtain ⟨-, K, hK, hcov⟩ := hΓ
  rw [Metric.continuous_iff']
  intro x₀ ε hε

  have hnear : ∀ᶠ x in nhds x₀, ∀ k ∈ K, dist (F (x, k)) (F (x₀, k)) < ε / 2 := by
    refine hK.eventually_forall_of_forall_eventually fun k _ => ?_
    have h1 : ∀ᶠ z : X × G in nhds (x₀, k), dist (F z) (F (x₀, k)) < ε / 4 :=
      Metric.tendsto_nhds.mp (hF.tendsto (x₀, k)) _ (by positivity)
    have h2 : ∀ᶠ z : X × G in nhds (x₀, k), dist (F (x₀, z.2)) (F (x₀, k)) < ε / 4 :=
      Metric.tendsto_nhds.mp (((hsec x₀).comp continuous_snd).tendsto (x₀, k)) _ (by positivity)
    filter_upwards [h1, h2] with z hz1 hz2
    calc dist (F (z.1, z.2)) (F (x₀, z.2))
        ≤ dist (F (z.1, z.2)) (F (x₀, k)) + dist (F (x₀, z.2)) (F (x₀, k)) :=
          dist_triangle_right _ _ _
      _ < ε / 4 + ε / 4 := add_lt_add hz1 hz2
      _ = ε / 2 := by ring
  filter_upwards [hnear] with x hx

  have hall : ∀ y : G, ‖F (x, y) - F (x₀, y)‖ ≤ ε / 2 := by
    intro y
    obtain ⟨γ, hγ, hγK⟩ := hcov y
    rw [← hper x γ hγ y, ← hper x₀ γ hγ y, ← dist_eq_norm]
    exact (hx _ hγK).le
  rw [dist_eq_norm, ← integral_sub (hfacts x).2.2.1 (hfacts x₀).2.2.1]
  calc ‖∫ y in D, (F (x, y) - F (x₀, y)) ∂μ‖ ≤ ε / 2 * μ.real D :=
        norm_setIntegral_le_of_norm_le_const (lt_top_iff_ne_top.mpr (hfacts x).2.1)
          fun y _ => hall y
    _ = ε / 2 := by simp [Measure.real, hD1]
    _ < ε := half_lt_self hε

end GlobalTheory.CuspGeneric
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousQuotientAveragePeriodicFamilyStatement
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_quotientAverage_periodic_family : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] (Γ : AddSubgroup G), IsCoLat Γ → ∀ (X : Type) [TopologicalSpace X] (F : X × G → ℂ), Continuous F → (∀ x, ∀ γ ∈ Γ, ∀ y, F (x, γ + y) = F (x, y)) → Continuous fun x => avg Γ (fun y => F (x, y)) := by
  first | exact @GlobalTheory.CuspGeneric.continuous_avg_of_periodic | exact GlobalTheory.CuspGeneric.continuous_avg_of_periodic | (intros; apply GlobalTheory.CuspGeneric.continuous_avg_of_periodic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoLocalConditionAllLocalizations
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoLocalConditionAllLocalizations
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.AdmBK

theorem litGoodO_all : LitGoodO := fun l _ LL => (GlobalTheory.LocalIntegers.good_integers l LL).1

theorem blochKato_dimFormula_all_finiteExt_coeffField (D : D7) : TruncatedSeriesCountingBounds.adm8 D := fun l _ K LL _ =>
  GlobalTheory.BlochKatoTied.blochKatoDim_of_tied l (D.loc l) (D.locA l) (D.locT l) K LL

theorem admBK_loc_of_blochKato_tateDuality_euler : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK →
    Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.admBK i := by
  intro hBK hTD hEC D i
  exact bloch_kato_annihilators_of D i (GlobalTheory.BlochKatoLocalOfHyp.blochKatoLocal_allPrimes_of_blochKato hBK hTD hEC D)
    (fun l _ K => GlobalTheory.TateTop.tateH2_of_duality_loc hTD l (D.loc l) K) (blochKato_dimFormula_all_finiteExt_coeffField D) litGoodO_all

end GlobalTheory.AdmBK
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoLocalConditionAllLocalizationsStatement
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blochKato_localCondition_all_localizations : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.admBK i := by
  first | exact @GlobalTheory.AdmBK.admBK_loc_of_blochKato_tateDuality_euler | exact GlobalTheory.AdmBK.admBK_loc_of_blochKato_tateDuality_euler | (intros; apply GlobalTheory.AdmBK.admBK_loc_of_blochKato_tateDuality_euler <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fGeneratedLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fGeneratedLattice
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.H1fGeneration


set_option maxHeartbeats 1000000 in
theorem h1fGen_tied : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)] (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) [IsTopologicalAddGroup T.V], FiniteCohomologyGeneratorsBound (P.PD K) T.L := by
  intro l _ P AI hT K LL _ T _ hG hC hcont
  have hO := (GlobalTheory.LocalIntegers.good_integers l LL).1
  have hDR := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI hT K LL T.V T.ρ hC).1
  obtain ⟨s, hs, hcard⟩ := GlobalTheory.T.h1fT_span_card_bound l P AI hT K (↥LL.1) (↥(OL LL)) hO T hDR
  have hBK := GlobalTheory.T.blochKatoDimensionFormula_concretePeriodRings l P AI hT K LL hG.1 T.V T.ρ hcont hC
  refine ⟨s, hs, ?_⟩
  have h0 : (0 : ℤ) ≤ (finrank ↥LL.1 ↥(H0V T.ρ) : ℤ) := by positivity
  set_option synthInstance.maxHeartbeats 200000 in
    have hc : ((s.card + finrank ↥LL.1 ↥(H0V T.ρ) : ℕ) : ℤ) ≤ ((finrank ↥LL.1 (FiniteCohomology (P.PD K) T.ρ) + finrank ↥LL.1 T.V : ℕ) : ℤ) := by
      exact_mod_cast hcard
    push_cast at hc
    linarith

end GlobalTheory.H1fGeneration
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fGeneratedLatticeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.h1f_generated_lattice : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)] (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) [IsTopologicalAddGroup T.V], FiniteCohomologyGeneratorsBound (P.PD K) T.L := by
  first | exact @GlobalTheory.H1fGeneration.h1fGen_tied | exact GlobalTheory.H1fGeneration.h1fGen_tied | (intros; apply GlobalTheory.H1fGeneration.h1fGen_tied <;> assumption)
end
end
