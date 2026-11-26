module

public import Formalism.LocalToGlobal.Columns.Inputs
public import Formalism.GL3MeanSquares.HookFormulaTorsion.SumWeightsOverPrimeLeHalfDegree
public import Formalism.HermitianLattices.FinalMass
public import Formalism.LocalToGlobal.Columns.LocWLemmas
public import Formalism.LocalToGlobal.Columns.ToHLat

@[expose] public section

section -- merged from Formalism.LocalToGlobal.Columns.CmUnramifiedOfFieldConditions
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Frame

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

structure LinOn (w : HeightOneSpectrum (𝓞 K)) (N : Submodule (𝓞 K) V) {A : Type} [AddCommGroup A]
    [Module (𝓞 K ⧸ w.asIdeal) A] (g : V → A) : Prop where
  add : ∀ x ∈ N, ∀ y ∈ N, g (x + y) = g x + g y
  smul : ∀ (a : 𝓞 K), ∀ x ∈ N, g (a • x) = Ideal.Quotient.mk w.asIdeal a • g x

namespace LinOn

variable {w : HeightOneSpectrum (𝓞 K)} {N : Submodule (𝓞 K) V} {A : Type} [AddCommGroup A]
  [Module (𝓞 K ⧸ w.asIdeal) A] {g : V → A}

end LinOn

end Frame

section Fibre

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

end Fibre

section Abstract

variable {A H D D₀ : Type} [Group A] [Group H] [MulAction (A × H) D] [MulAction A D₀]

end Abstract

section Mass

variable (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ)

abbrev UniLat : Type :=
  {N : Submodule (𝓞 E) (Sp E n) // Submodule.IsLattice E N ∧ IsUnimodular (hStd E n) N}

variable {E n}

theorem gmap_unimodular {g : Sp E n ≃ₗ[E] Sp E n} (hg : g ∈ UF E n) {N : Submodule (𝓞 E) (Sp E n)}
    (hN : IsUnimodular (hStd E n) N) : IsUnimodular (hStd E n) (gmap g N) := by
  unfold Formalism.HermitianLatticesTheory.IsUnimodular at *
  rw [dual_gmap g hg, hN]

instance : MulAction (UF E n) (UniLat E n) where
  smul g N := ⟨gmap g.1 N.1, gmap_lattice g.1 N.1 N.2.1, gmap_unimodular g.2 N.2.2⟩
  one_smul N := Subtype.ext (Submodule.map_id N.1)
  mul_smul a b N := Subtype.ext (by
    change N.1.map _ = (N.1.map _).map _
    rw [← Submodule.map_comp]
    rfl)

variable (E n)

abbrev autU (N : UniLat E n) : Subgroup (UF E n) := MulAction.stabilizer (UF E n) N

variable {E n}

theorem finite_autU (hE : PosStar E) (N : UniLat E n) : Finite (autU E n N) := by
  have hA := final_autFinite E (Sp E n) (hStd E n) hStd_isSymm (hStd_pos hE) N.1
    (hcnt_isFullLattice_of_unimodular N.2.1 N.2.2)
  have : Finite {g : Sp E n ≃ₗ[E] Sp E n | g ∈ isom (hStd E n) ∧ gmap g N.1 = N.1} := hA
  refine Finite.of_injective
    (fun a : autU E n N => (⟨a.1.1, a.1.2, congrArg Subtype.val a.2⟩ :
      {g : Sp E n ≃ₗ[E] Sp E n | g ∈ isom (hStd E n) ∧ gmap g N.1 = N.1})) ?_
  intro a b hab
  exact Subtype.ext (Subtype.ext (show a.1.1 = b.1.1 from
    congrArg (fun g : {g : Sp E n ≃ₗ[E] Sp E n | g ∈ isom (hStd E n) ∧ gmap g N.1 = N.1} => g.1) hab))

end Mass

section MassGenus

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

end MassGenus

section Count

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

def DecoSet.lat (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) : UniLat E n := ⟨d.1.N, d.2.lat, d.2.uni⟩


end Count

section Idx

variable {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 E))}
  (Λ : LevFam E K n SG)

end Idx

section FormCount

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG)

end FormCount

section IdxQ

theorem card_res {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    Nat.card (𝓞 E ⧸ w.asIdeal) = Ideal.absNorm w.asIdeal := by
  exact (Ideal.absNorm_eq_natCard w.asIdeal).symm

end IdxQ

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks}

theorem rankN_zero (R : Ranks) : R.N 0 = R.k := by
  simp [Ranks.N]



variable (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Cols

section Inst

open Finset Formalism.LogVandermondeBounds.StandardLattice

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

theorem vandN_congr {x y : ℕ → ℝ} {N : ℕ} (h : ∀ i j, i < N → j < N → x i - x j = y i - y j) : vandN x N = vandN y N := by
  unfold vandN
  exact Finset.prod_congr rfl fun i hi => Finset.prod_congr rfl fun j hj =>
    h i j (Finset.mem_range.1 hi) (Finset.mem_Ico.1 hj).2

end Inst

section Rows

open Finset Formalism.LogVandermondeBounds.StandardLattice

variable {X : Fields} {Pr : Primes X} {R : Ranks}



variable (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

end Rows

section WeylTest

open Finset Formalism.LogVandermondeBounds.StandardLattice Formalism.GradedWeylDivisibility

end WeylTest

section Unram

theorem cm_unramified_of_field_conditions {X : Fields} (hX : X.AbelianUnramifiedExtensionConditions) : IsCMUnram X.E := by
  refine ⟨hX.ok.cplxE, hX.ok.conjE, ?_⟩
  intro P hP
  by_contra hcon
  have hall : ∀ θ : 𝓞 X.E, θ - X.conjO θ ∈ P := by
    intro θ
    by_contra h
    exact hcon ⟨θ, X.conjO θ, rfl, h⟩
  have hq : Algebra.IsQuadraticExtension X.F X.E := { finrank_eq_two' := hX.ok.rankE }
  let c : Gal(X.E/X.F) := AlgEquiv.ofRingEquiv (f := starRingAut) (fun r => hX.ok.star_F r)
  have hP0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField X.E)
  have hPp : P.IsPrime := hP.isPrime
  have hun := hX.unram ⟨P, hPp, hP0⟩
  have hlo : P.LiesOver (P.under (𝓞 X.F)) := ⟨rfl⟩
  have hp0 : P.under (𝓞 X.F) ≠ ⊥ := Ideal.IsIntegral.comap_ne_bot (𝓞 X.F) hP0
  have hcard : Nat.card (P.inertia Gal(X.E/X.F)) = 1 := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(X.E/X.F)) (P.under (𝓞 X.F)) P,
      Ideal.ramificationIdxIn_eq_ramificationIdx (P.under (𝓞 X.F)) P Gal(X.E/X.F),
      ← Ideal.ramificationIdx'_eq_ramificationIdx (P.under (𝓞 X.F)) P hp0]
    by_contra h
    exact hun ((Ideal.ramificationIdx'_ne_one_iff Ideal.map_comap_le).mp h)
  have hc : c ∈ P.inertia Gal(X.E/X.F) := by
    intro x
    have h1 : c • x - x = -(x - X.conjO x) := by
      rw [neg_sub]
      rfl
    rw [h1]
    exact P.neg_mem (hall x)
  have hc1 : c = 1 := by
    have hb := (Subgroup.card_eq_one (H := P.inertia Gal(X.E/X.F))).mp hcard
    rw [hb] at hc
    exact hc
  have hτ : Nonempty X.Tau := by
    rw [← Fintype.card_pos_iff, hX.ok.card_Tau]
    exact Module.finrank_pos
  obtain ⟨τ⟩ := hτ
  apply hX.ok.emb_ne τ τ
  ext x
  have h2 : star x = x := congrArg (fun s : Gal(X.E/X.F) => s x) hc1
  show X.emb τ x = X.emb τ (star x)
  rw [h2]

end Unram

section Weighted

variable {A H D D₀ : Type} [Group A] [Group H] [MulAction (A × H) D] [MulAction A D₀]

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG)

end Weighted

section Whole

end Whole

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.AdjointFrobeniusPreservesRamified
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.LogVandermondeBounds

section CoordLemmas

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}
  {N : Submodule (𝓞 E) (Sp E n)}

theorem FunAt.of_smul_mem {f : Sp E n → 𝓞 E ⧸ P.asIdeal} (h : FunAt P N f) {z : Sp E n}
    (hz : z ∈ P.asIdeal • N) : f z = 0 := by
  have key : z ∈ N ∧ f z = 0 := by
    refine Submodule.smul_induction_on hz (fun p hp y hy => ?_) (fun y y' hy hy' => ?_)
    · refine ⟨N.smul_mem p hy, ?_⟩
      rw [h.smul p y (le_locP _ _ hy), Ideal.Quotient.eq_zero_iff_mem.2 hp, zero_mul]
    · refine ⟨N.add_mem hy.1 hy'.1, ?_⟩
      rw [h.add y (le_locP _ _ hy.1) y' (le_locP _ _ hy'.1), hy.2, hy'.2, add_zero]
  exact key.2

variable {co : Sp E n → (Fin n → 𝓞 E ⧸ P.asIdeal)}

theorem CoordAt.comp (h : CoordAt P N co) (i : Fin n) : FunAt P N fun y => co y i := by
  exact ⟨fun x hx y hy => congrFun (h.add x hx y hy) i,
    fun a x hx => congrFun (h.smul a x hx) i,
    fun x hx => congrFun (h.off x hx) i⟩

theorem CoordAt.of_smul_mem (h : CoordAt P N co) {z : Sp E n} (hz : z ∈ P.asIdeal • N) : co z = 0 :=
  funext fun i => (h.comp i).of_smul_mem hz

end CoordLemmas

section FibLemmas

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

variable {d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)} {P : ST} {q : 𝓞 E} {co : Sp E n → (Fin n → 𝓞 E ⧸ P.1.asIdeal)}

end FibLemmas

section FibModel

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}
  {d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)} {P : ST} {q : 𝓞 E} {co : Sp E n → (Fin n → 𝓞 E ⧸ P.1.asIdeal)}

end FibModel

section Exists

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem intAt_algebraMap_ow (P : HeightOneSpectrum (𝓞 E)) (r : Ow P) : IntAt P (algebraMap (Ow P) E r) := by
  obtain ⟨a, t, rfl⟩ := IsLocalization.exists_mk'_eq P.asIdeal.primeCompl r
  refine ⟨a, t, t.2, ?_⟩
  rw [IsScalarTower.algebraMap_apply (𝓞 E) (Ow P) E, ← map_mul, mul_comm, IsLocalization.mk'_spec,
    ← IsScalarTower.algebraMap_apply]

theorem exists_locBasis (P : HeightOneSpectrum (𝓞 E)) {N : Submodule (𝓞 E) (Sp E n)}
    (hN : Submodule.IsFullLattice E N) :
    ∃ β : Module.Basis (Fin n) E (Sp E n), (∀ i, β i ∈ localization₂ P.asIdeal N) ∧
      ∀ y ∈ localization₂ P.asIdeal N, ∀ i, IntAt P (β.repr y i) := by
  classical
  obtain ⟨ι, _, b, bK, hb⟩ := exists_basis_atW P hN.toIsLattice.fg hN.span_eq_top
  have hcard : Fintype.card ι = n := by
    rw [← Module.finrank_eq_card_basis bK, Module.finrank_fin_fun]
  let e : ι ≃ Fin n := Fintype.equivFinOfCardEq hcard
  refine ⟨bK.reindex e, fun i => ?_, fun y hy i => ?_⟩
  · rw [Module.Basis.reindex_apply, hb]
    exact (mem_locP _ _ _).2 (mem_atW_iff.1 (b (e.symm i)).2)
  · have hy' : y ∈ atW P N := mem_atW_iff.2 ((mem_locP _ _ _).1 hy)
    have h1 : (∑ j, b.repr ⟨y, hy'⟩ j • b j) = (⟨y, hy'⟩ : atW P N) := b.sum_repr _
    have h2 : y = ∑ j, algebraMap (Ow P) E (b.repr ⟨y, hy'⟩ j) • bK j := by
      have h3 := congrArg (fun z : atW P N => (z : Sp E n)) h1
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h3
      refine h3.symm.trans ?_
      exact Finset.sum_congr rfl fun j _ => by rw [hb, ow_smul_def]
    have h4 : bK.repr y (e.symm i) = algebraMap (Ow P) E (b.repr ⟨y, hy'⟩ (e.symm i)) := by
      have h5 := congrArg (fun z => bK.repr z (e.symm i)) h2
      simp only [Module.Basis.repr_sum_self] at h5
      exact h5
    rw [Module.Basis.repr_reindex_apply, h4]
    exact intAt_algebraMap_ow P _

theorem exists_coordAt (P : HeightOneSpectrum (𝓞 E)) {N : Submodule (𝓞 E) (Sp E n)}
    (hN : Submodule.IsFullLattice E N) : ∃ co, CoordAt P N co := by
  classical
  obtain ⟨β, hβ, hint⟩ := exists_locBasis P hN
  let co : Sp E n → (Fin n → 𝓞 E ⧸ P.asIdeal) := fun y =>
    if y ∈ localization₂ P.asIdeal N then fun i => redP P (β.repr y i) else 0
  have hpos : ∀ y, y ∈ localization₂ P.asIdeal N → co y = fun i => redP P (β.repr y i) := fun y hy => if_pos hy
  have hsm : ∀ (a : 𝓞 E), ∀ x ∈ localization₂ P.asIdeal N, co (a • x) = Ideal.Quotient.mk P.asIdeal a • co x := by
    intro a x hx
    rw [hpos _ (Submodule.smul_mem _ a hx), hpos _ hx]
    funext i
    rw [← algebraMap_smul E a x, map_smul, Finsupp.smul_apply, smul_eq_mul, ← Algebra.smul_def,
      redP_osmul a (hint x hx i)]
    rfl
  refine ⟨co, ⟨?_, hsm, fun x hx => if_neg hx, ?_, ?_⟩⟩
  · intro x hx y hy
    rw [hpos _ (Submodule.add_mem _ hx hy), hpos _ hx, hpos _ hy]
    funext i
    rw [map_add (f := _), Finsupp.add_apply, reduction_add (hint x hx i) (hint y hy i)]
    rfl
  · intro c
    choose r hr using fun i => Ideal.Quotient.mk_surjective (c i)
    have hy0 : ∑ i, r i • β i ∈ localization₂ P.asIdeal N := Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hβ i)
    have hc0 : co (∑ i, r i • β i) = c := by
      rw [hpos _ hy0]
      funext i
      have : (∑ i, r i • β i) = ∑ i, algebraMap (𝓞 E) E (r i) • β i :=
        Finset.sum_congr rfl fun i _ => (algebraMap_smul E _ _).symm
      rw [this, Module.Basis.repr_sum_self, reduction_coe, hr]
    obtain ⟨s, hs, hsy⟩ := (mem_locP _ _ _).1 hy0
    have := P.isMaximal
    obtain ⟨t', ht'⟩ := Ideal.Quotient.exists_inv (mk_ne_zero hs)
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective t'
    refine ⟨t • s • ∑ i, r i • β i, N.smul_mem t hsy, ?_⟩
    rw [hsm t _ (Submodule.smul_mem _ s hy0), hsm s _ hy0, hc0, smul_smul, mul_comm, ht', one_smul]
  · intro x hx h0
    have hxl := le_locP P N hx
    rw [hpos _ hxl] at h0
    have hterm : ∀ i, β.repr x i • β i ∈ localization₂ P.asIdeal (P.asIdeal • N) := by
      intro i
      obtain ⟨r, s, hs, hrs⟩ := hint x hxl i
      have hr : r ∈ P.asIdeal := by
        have h1 := reduction_spec P hs hrs
        rw [congrFun h0 i] at h1
        simp only [Pi.zero_apply, mul_zero] at h1
        exact Ideal.Quotient.eq_zero_iff_mem.1 h1.symm
      obtain ⟨s', hs', hb⟩ := (mem_locP _ _ _).1 (hβ i)
      refine (mem_locP _ _ _).2 ⟨s * s', fun hm => (P.isPrime.mem_or_mem hm).elim hs hs', ?_⟩
      have e : (s * s') • (β.repr x i • β i) = r • (s' • β i) := by
        rw [mul_smul, smul_comm s' (β.repr x i) (β i), ← algebraMap_smul E s, smul_smul, hrs, algebraMap_smul]
      rw [e]
      exact Submodule.smul_mem_smul hr hb
    have hsum : x ∈ localization₂ P.asIdeal (P.asIdeal • N) := by
      rw [← β.sum_repr x]
      exact Submodule.sum_mem _ fun i _ => hterm i
    obtain ⟨s, hs, hsx⟩ := (mem_locP _ _ _).1 hsum
    exact mem_smul_of_loc hx hs hsx

end Exists

section Apply

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG)

end Apply

section Dict

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  {C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))} {Λ : LevFam X.E X.K n SG}

attribute [local instance] resField resFintype

open Classical

variable {P : ST} {q : 𝓞 X.E} {d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)} {co : Sp X.E n → (Fin n → 𝓞 X.E ⧸ P.1.asIdeal)}
  {R : Type} [CommRing R] {σ : X.K →+* R}

end Dict

section T1

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG)

attribute [local instance] resField resFintype

open Classical

variable {P : ST} {q : 𝓞 X.E}

section Lin

variable {C Λ} {d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)} {co : Sp X.E n → (Fin n → 𝓞 X.E ⧸ P.1.asIdeal)}
  {R : Type} [CommRing R] {σ : X.K →+* R}

end Lin

end T1

section T7

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG)

attribute [local instance] resField resFintype

open Classical

variable {P : ST} {q : 𝓞 X.E}

section DictC

variable {C Λ} {d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)} {co : Sp X.E n → (Fin n → 𝓞 X.E ⧸ P.1.asIdeal)} {σ : X.K →+* ℂ}

end DictC

end T7

section ColsT1

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

variable (Ps : CharT X Pr)

end ColsT1

section AdjA
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

end AdjA

section AdjB
variable {X : Fields}

end AdjB

section AdjC
variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (Ps : CharT X Pr)

end AdjC

section AdjD
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K)

end AdjD

section AdjF
variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (Ps : CharT X Pr)

end AdjF

section RamStable

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (Ps : CharT X Pr)

end RamStable

end Formalism.L2.Col
end
end
