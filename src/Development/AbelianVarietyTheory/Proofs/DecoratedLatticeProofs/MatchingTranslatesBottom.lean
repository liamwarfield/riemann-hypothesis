module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormaliserCore
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarComplementFrameDiagModConductor

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SettingNormaliser
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdPlaces
noncomputable section

open Formalism.BasicNotions IsDedekindDomain NumberField Matrix Formalism.L2.DIV Formalism.IndefR.Lev GlobalTheory.StdFrames GlobalTheory.AdIsom
open scoped TensorProduct

namespace GlobalTheory.LevNorm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

@[reducible] def kField {E : Type} [Field E] [NumberField E] (Q : Pl E) : Field (kP Q) :=
  haveI := Q.isMaximal
  Ideal.Quotient.field Q.asIdeal

attribute [local instance] kField

def adPlaces (D : D7) : PlaceSys (EAf D) (Formalism.L2.Herm.intAf D.host.F D.host.E) (Pl D.host.E) (fun Q => kP Q)
    (fun Q => resS D.host.F Q) where
  K Q := Q.adicCompletion D.host.E
  O Q := Q.adicCompletionIntegers D.host.E
  p Q := cpt Q
  e Q := idem Q
  surj Q x := by
    classical
    obtain ⟨z, hz⟩ := GlobalTheory.AdeleBaseChange.map_surjective (toAd_spec D)
      (⟨Pi.single Q x, by
        refine Filter.mem_of_superset (Set.finite_singleton Q).compl_mem_cofinite fun Q' h => ?_
        show (Pi.single Q x : ∀ v : Pl D.host.E, v.adicCompletion D.host.E) Q' ∈ Q'.adicCompletionIntegers D.host.E
        rw [Pi.single_eq_of_ne h]
        exact zero_mem _⟩ : FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    refine ⟨z, ?_⟩
    change toAd D z Q = _
    rw [hz]
    exact Pi.single_eq_same (M := fun v : Pl D.host.E => v.adicCompletion D.host.E) Q x
  e_self Q := ((isPlIdem_iff Q _).1 (isPlIdem_idem Q)).1
  e_ne Q := ((isPlIdem_iff Q _).1 (isPlIdem_idem Q)).2
  ext a h := cpt_ext fun Q => by rw [h Q, map_zero]
  int a := mem_OA a
  fin a := Filter.eventually_cofinite.1 (toAd D a).2
  r_surj Q y := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨_, resS_oToS Q x⟩
  r_ker Q s := (resS_eq_zero_iff_cpt Q s).trans
    ((Valuation.isEquiv_valuation_valuationSubring Valued.v).lt_one_iff_lt_one)

end GlobalTheory.LevNorm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GenusTypePlacesPairwiseNotConjugate
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GenusTypePlacesPairwiseNotConjugate
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi

theorem typePlaces_noConj : ∀ (D : D7) (Pg : Finset (Pl D.host.E)), GlobalTheory.Core.Mi.IsTypePlaces Pg →
    ∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ IsConjPl (D := D) PP PP' := by
  intro D Pg hT PP hP PP' hP' hc
  have hstar : ∀ z : D.host.E, star z = D.host.conj z := Formalism.BasicNotions.bridge_star_holds D.R D.host
  have hFfix : ∀ r : 𝓞 D.host.F,
      D.host.conj ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r : 𝓞 D.host.E) : D.host.E) =
        ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r : 𝓞 D.host.E) : D.host.E) :=
    fun r => (D.host.conjE_mem_hostF_iff _).1 (r : D.host.F).2

  have hle : PP.asIdeal.under (𝓞 D.host.F) ≤ PP'.asIdeal.under (𝓞 D.host.F) := by
    intro r hr
    rw [Ideal.under_def, Ideal.mem_comap] at hr ⊢
    obtain ⟨c', hc', he⟩ := hc _ hr
    have : c' = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) r := by
      apply RingOfIntegers.ext
      rw [he, hstar, hFfix]
    rwa [← this]
  have hmax : (PP.asIdeal.under (𝓞 D.host.F)).IsMaximal := by
    rw [← HeightOneSpectrum.under_asIdeal]
    exact (HeightOneSpectrum.under (𝓞 D.host.F) PP).isMaximal
  have hne : PP'.asIdeal.under (𝓞 D.host.F) ≠ ⊤ := by
    rw [← HeightOneSpectrum.under_asIdeal]
    exact (HeightOneSpectrum.under (𝓞 D.host.F) PP').isPrime.ne_top
  have hund : HeightOneSpectrum.under (𝓞 D.host.F) PP' = HeightOneSpectrum.under (𝓞 D.host.F) PP := by
    apply HeightOneSpectrum.ext
    rw [HeightOneSpectrum.under_asIdeal, HeightOneSpectrum.under_asIdeal]
    exact (hmax.eq_of_le hne hle).symm
  have hgP := hT.1 PP hP
  have hgv : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ (HeightOneSpectrum.under (𝓞 D.host.F) PP).asIdeal := by
    rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact hgP
  obtain ⟨W, _, hW⟩ := hT.2 _ hgv
  have e1 : PP = W := hW PP ⟨hP, rfl⟩
  have e2 : PP' = W := hW PP' ⟨hP', hund⟩
  have e : PP' = PP := e2.trans e1.symm
  subst e

  obtain ⟨k, hk⟩ : ∃ k : Fin 2, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP'.asIdeal := by
    rw [Nat.cast_mul] at hgP
    rcases PP'.isPrime.mem_or_mem hgP with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨x, hx, hxn⟩ :=
    (GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) (D.host.g_prime k) (D.nd.g_split k) PP' hk).2.2.1
  obtain ⟨c', hc', he⟩ := hc x hx
  exact hxn c' (he.trans (hstar _)) hc'

end GlobalTheory.Core.Mi
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GenusTypePlacesPairwiseNotConjugateStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genus_type_places_pairwise_not_conjugate : ∀ (D : D7) (Pg : Finset (Pl D.host.E)), GlobalTheory.Core.Mi.IsTypePlaces Pg → ∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ IsConjPl (D := D) PP PP' := by
  first | exact @GlobalTheory.Core.Mi.typePlaces_noConj | exact GlobalTheory.Core.Mi.typePlaces_noConj | (intros; apply GlobalTheory.Core.Mi.typePlaces_noConj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegerSubConjNotMemSelfConjugatePlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegerSubConjNotMemSelfConjugatePlace
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjMovesResidue

theorem exists_sub_star_notMem : ∀ (D : D7) (Q : Pl D.host.E), IsConjPl (D := D) Q Q →
    ∃ δ δ' : 𝓞 D.host.E, (δ' : D.host.E) = star (δ : D.host.E) ∧ δ - δ' ∉ Q.asIdeal := by
  intro D Q _
  obtain ⟨θ, t, h1, h2⟩ := Formalism.BasicNotions.Examples₂.unram_at D.host Q.asIdeal Q.isMaximal
  refine ⟨θ, t, ?_, h2⟩
  change algebraMap (𝓞 D.host.E) D.host.E t = _
  rw [h1, Formalism.BasicNotions.Examples₂.star_eq_conj]

end GlobalTheory.ConjMovesResidue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegerSubConjNotMemSelfConjugatePlaceStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integer_sub_conj_notMem_self_conjugate_place : ∀ (D : D7) (Q : Pl D.host.E), IsConjPl (D := D) Q Q → ∃ δ δ' : 𝓞 D.host.E, (δ' : D.host.E) = star (δ : D.host.E) ∧ δ - δ' ∉ Q.asIdeal := by
  first | exact @GlobalTheory.ConjMovesResidue.exists_sub_star_notMem | exact GlobalTheory.ConjMovesResidue.exists_sub_star_notMem | (intros; apply GlobalTheory.ConjMovesResidue.exists_sub_star_notMem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryGroupConjugateTransposeMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicHatMulOfMulClosed
noncomputable section

namespace GlobalTheory.AdelicLatticeClosure

open NumberField IsDedekindDomain
open scoped TensorProduct

theorem adelic_hat_mul_of_mul_closed {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (J : Set E) (hJ : ∀ x ∈ J, ∀ y ∈ J, x * y ∈ J) {z w : GlobalTheory.AdLat.RA F E}
    (hz : z ∈ GlobalTheory.AdLat.hat1 F J) (hw : w ∈ GlobalTheory.AdLat.hat1 F J) :
    z * w ∈ GlobalTheory.AdLat.hat1 F J := by
  unfold GlobalTheory.AdLat.hat1 at hz hw ⊢
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨b, hb, y, hy, rfl⟩ := hw
      refine AddSubgroup.subset_closure ⟨a * b, fun v => ?_, x * y, hJ x hx y hy, ?_⟩
      · exact mul_mem (ha v) (hb v)
      · exact Algebra.TensorProduct.tmul_mul_tmul a b x y
    | zero => rw [mul_zero]; exact zero_mem _
    | add u v _ _ hu hv => rw [mul_add]; exact add_mem hu hv
    | neg u _ hu => rw [mul_neg]; exact neg_mem hu
  | zero => rw [zero_mul]; exact zero_mem _
  | add u v _ _ hu hv => rw [add_mul]; exact add_mem hu hv
  | neg u _ hu => rw [neg_mul]; exact neg_mem hu

theorem adelic_hat_one_mul_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {z w : GlobalTheory.AdLat.RA F E}
    (hz : z ∈ GlobalTheory.AdLat.hat1 F
      (↑(1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E))
    (hw : w ∈ GlobalTheory.AdLat.hat1 F
      (↑(1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E)) :
    z * w ∈ GlobalTheory.AdLat.hat1 F
      (↑(1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E) := by
  refine adelic_hat_mul_of_mul_closed _ ?_ hz hw
  intro x hx y hy
  obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
  obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hy
  exact (FractionalIdeal.mem_one_iff _).2 ⟨a * b, map_mul _ a b⟩

end GlobalTheory.AdelicLatticeClosure
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryGroupConjugateTransposeMatrix
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GramFrame

section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem integral_adelic_lattice_mul_mem {z w : GlobalTheory.AdLat.RA F E}
    (hz : z ∈ GlobalTheory.AdLat.hat1 F ((1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E))
    (hw : w ∈ GlobalTheory.AdLat.hat1 F ((1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E)) :
    z * w ∈ GlobalTheory.AdLat.hat1 F ((1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E) := by
  exact GlobalTheory.AdelicLatticeClosure.adelic_hat_one_mul_mem hz hw

theorem one_int_af : ∀ v : HeightOneSpectrum (𝓞 F),
    (1 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F := fun v => by
  show (1 : v.adicCompletion F) ∈ _
  exact one_mem _

theorem mem_integral_adelic_lattice_iff (z : GlobalTheory.AdLat.RA F E) :
    z ∈ GlobalTheory.AdLat.hat1 F ((1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E) ↔
      GlobalTheory.LevSplit.swp F E z ∈ Formalism.L2.Herm.intAf F E := by
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hz
      obtain ⟨x', rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
      rw [GlobalTheory.LevSplit.swp_tmul]
      have e : (algebraMap (𝓞 E) E x') ⊗ₜ[F] a =
          ((algebraMap (𝓞 E) E x') ⊗ₜ[F] (1 : Formalism.L2.Herm.Af F)) * ((1 : E) ⊗ₜ[F] a) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      rw [e]
      refine mul_mem (Subring.subset_closure (Or.inl ⟨⟨_, x', rfl⟩, rfl⟩))
        (Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩))
    | zero => rw [map_zero]; exact zero_mem _
    | add u u' _ _ hu hu' => rw [map_add]; exact add_mem hu hu'
    | neg u _ hu => rw [map_neg]; exact neg_mem hu
  · intro hz
    have key : ∀ s ∈ Formalism.L2.Herm.intAf F E, ∃ t ∈ GlobalTheory.AdLat.hat1 F
        ((1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Set E), GlobalTheory.LevSplit.swp F E t = s := by
      intro s hs
      induction hs using Subring.closure_induction with
      | mem s hs =>
        rcases hs with ⟨⟨_, c, rfl⟩, rfl⟩ | ⟨⟨b, hb⟩, rfl⟩
        · exact ⟨(1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (algebraMap (𝓞 E) E c),
            AddSubgroup.subset_closure ⟨1, one_int_af, _, (FractionalIdeal.mem_one_iff _).2 ⟨c, rfl⟩, rfl⟩, rfl⟩
        · exact ⟨b ⊗ₜ[F] (1 : E), AddSubgroup.subset_closure ⟨b, hb, 1,
            (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩, rfl⟩, rfl⟩
      | zero => exact ⟨0, zero_mem _, map_zero _⟩
      | one => exact ⟨1, AddSubgroup.subset_closure ⟨1, one_int_af, 1,
            (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩, rfl⟩, map_one _⟩
      | add a b _ _ ha hb =>
        obtain ⟨t, ht, rfl⟩ := ha
        obtain ⟨t', ht', rfl⟩ := hb
        exact ⟨t + t', add_mem ht ht', map_add _ _ _⟩
      | neg a _ ha =>
        obtain ⟨t, ht, rfl⟩ := ha
        exact ⟨-t, neg_mem ht, map_neg _ _⟩
      | mul a b _ _ ha hb =>
        obtain ⟨t, ht, rfl⟩ := ha
        obtain ⟨t', ht', rfl⟩ := hb
        exact ⟨t * t', integral_adelic_lattice_mul_mem ht ht', map_mul _ _ _⟩
    obtain ⟨t, ht, e⟩ := key _ hz
    rwa [GlobalTheory.LevSplit.swp_bij.1 e] at ht

end Gen
end GlobalTheory.GramFrame

namespace GlobalTheory.GramFrame

def conjEquiv (I : AutInst) : Gal(I.E/I.F) :=
  AlgEquiv.ofAlgHom I.cm.sig I.cm.sig
    (AlgHom.ext fun x => by show star (star x) = x; exact star_star x)
    (AlgHom.ext fun x => by show star (star x) = x; exact star_star x)

theorem conjEquiv_apply (I : AutInst) (x : I.E) : conjEquiv I x = I.cm.sig x := rfl

theorem hatL_selfDual (I : AutInst) : GlobalTheory.ParahoricLift.HatSelfDual I.cm.sig I.J I.L := by
  have hJ : ∀ a b, I.cm.sig (I.J b a) = I.J a b := fun a b => by
    have := congrFun (congrFun I.J_herm a) b
    exact (by simpa [Formalism.UG.cT] using this : starRingEnd I.E (I.J b a) = I.J a b)
  refine GlobalTheory.ParahoricLift.hatL_selfDual_gen (conjEquiv I) I.cm.sig (fun _ => rfl) I.J I.L I.L_fg I.L_span
    (fun x => by show star (star x) = x; exact star_star x) (fun a b => ?_) (by rw [Matrix.det_transpose]; exact I.J_det)
    (fun v => ?_) (fun s hs => Formalism.UG.P.csDual_sig_mem I.cm.sig hs) mem_integral_adelic_lattice_iff
  · simp only [Matrix.transpose_apply, conjEquiv_apply]
    exact hJ a b
  · rw [I.L_dual v]
    refine forall₂_congr fun y _ => ?_
    rw [FractionalIdeal.mem_one_iff]
    have e : (∑ a, ∑ b, v a * I.Jᵀ a b * conjEquiv I (y b)) =
        Formalism.UG.hform (starRingEnd I.E) I.J y v := by
      unfold Formalism.UG.hform
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      simp only [Matrix.transpose_apply, conjEquiv_apply]
      show _ = star (y a) * _ * _
      have : I.cm.sig (y a) = star (y a) := rfl
      rw [this]; ring
    rw [e]
    rfl

end GlobalTheory.GramFrame

namespace GlobalTheory.GramFrame

theorem gram_frame_int : ∀ (I : AutInst) (β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)), IsFrame β I.L → ∃ G : GL (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E), ((Formalism.UG.bc (Formalism.L2.Herm.intAf I.F I.E).subtype G : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) = Formalism.UG.cT (sigA I) (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) * (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) := by
  intro I β hβ
  set σ := sigA I with hσ
  set JA : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) :=
    I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) with hJA
  set B : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) := (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) with hB
  set Gm := Formalism.UG.cT σ B * JA * B with hGm
  have hSD := hatL_selfDual I

  have hmem : ∀ a : Fin I.n → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F, (∀ i, a i ∈ Formalism.L2.Herm.intAf I.F I.E) →
      B *ᵥ a ∈ Formalism.L2.Herm.hatL (F := I.F) I.L := fun a ha => by
    refine (hβ _).2 fun i => ?_
    rw [Matrix.mulVec_mulVec, hB, Units.inv_mul, Matrix.one_mulVec]
    exact ha i
  have hsingle : ∀ k, ∀ i, (Pi.single k (1 : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) : Fin I.n → _) i ∈
      Formalism.L2.Herm.intAf I.F I.E := fun k i => by
    rw [Pi.single_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _

  have hG : ∀ i j, Gm i j ∈ Formalism.L2.Herm.intAf I.F I.E := fun i j => by
    rw [← Formalism.UG.P.hform_single σ Gm i j, hGm, ← Formalism.UG.P.hform_mulVec]
    exact (hSD _).1 (hmem _ (hsingle j)) _ (hmem _ (hsingle i))

  have hdet : IsUnit Gm.det := by
    have h1 : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).1 β.isUnit
    have h2 : IsUnit (Formalism.UG.cT σ B).det := by
      rw [Formalism.UG.cT, Matrix.det_transpose, show B.map σ = σ.mapMatrix B from rfl, ← RingHom.map_det]
      exact h1.map σ
    have h3 : IsUnit JA.det := by
      rw [hJA, show I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) = (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)).mapMatrix I.J from rfl, ← RingHom.map_det]
      exact (isUnit_iff_ne_zero.2 I.J_det).map _
    rw [hGm, Matrix.det_mul, Matrix.det_mul]
    exact (h2.mul h3).mul h1
  have hGi : Gm * Gm⁻¹ = 1 := Matrix.mul_nonsing_inv Gm hdet
  have hiG : Gm⁻¹ * Gm = 1 := Matrix.nonsing_inv_mul Gm hdet

  have hG' : ∀ i j, (Gm⁻¹) i j ∈ Formalism.L2.Herm.intAf I.F I.E := fun i j => by
    set c : Fin I.n → I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F := fun l => (Gm⁻¹) l j with hc
    have hx : B *ᵥ c ∈ Formalism.L2.Herm.hatL (F := I.F) I.L := by
      refine (hSD _).2 fun z hz => ?_
      have hz' := (hβ z).1 hz
      set a := ((β⁻¹ : GL (Fin I.n) _) : Matrix (Fin I.n) (Fin I.n) _) *ᵥ z with ha
      have hza : z = B *ᵥ a := by
        rw [ha, Matrix.mulVec_mulVec, hB, Units.mul_inv, Matrix.one_mulVec]
      rw [hza, Formalism.UG.P.hform_mulVec, ← hGm, Formalism.UG.P.hform_eq_dot]
      have e : Gm *ᵥ c = Pi.single j 1 := by
        funext k
        have := congrFun (congrFun hGi k) j
        rw [Matrix.mul_apply] at this
        simp only [Matrix.mulVec, dotProduct, hc, this, Pi.single_apply, Matrix.one_apply]
      rw [e]
      simp only [dotProduct, Function.comp_apply, Pi.single_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact Formalism.L2.SG.Pf.unitaryCongruence.sigA_mem I (hz' j)
    have := (hβ _).1 hx i
    rwa [Matrix.mulVec_mulVec, hB, Units.inv_mul, Matrix.one_mulVec] at this

  let S := Formalism.L2.Herm.intAf I.F I.E
  have inj : Function.Injective fun M : Matrix (Fin I.n) (Fin I.n) S => M.map S.subtype :=
    Matrix.map_injective S.subtype_injective
  refine ⟨⟨Matrix.of fun i j => ⟨Gm i j, hG i j⟩, Matrix.of fun i j => ⟨(Gm⁻¹) i j, hG' i j⟩, inj ?_, inj ?_⟩, ?_⟩
  · show Matrix.map _ S.subtype = Matrix.map _ S.subtype
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact hGi
  · show Matrix.map _ S.subtype = Matrix.map _ S.subtype
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact hiG
  · rfl

end GlobalTheory.GramFrame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryGroupConjugateTransposeMatrixStatement
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_group_conjugate_transpose_matrix : ∀ (I : AutInst) (β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)), IsFrame β I.L → ∃ G : GL (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E), ((Formalism.UG.bc (Formalism.L2.Herm.intAf I.F I.E).subtype G : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) = Formalism.UG.cT (sigA I) (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * I.J.map (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) * (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) := by
  first | exact @GlobalTheory.GramFrame.gram_frame_int | exact GlobalTheory.GramFrame.gram_frame_int | (intros; apply GlobalTheory.GramFrame.gram_frame_int <;> assumption)
end
end

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis Formalism.UG
open Formalism.L2.SG.Pf.unitaryCongruence
open scoped TensorProduct

namespace GlobalTheory.LevNorm

attribute [local instance] Formalism.BasicNotions.Host.cmStar kField

theorem mem_UJ_conj {A : Type} [CommRing A] (σ : A →+* A) {n : ℕ} (J : Matrix (Fin n) (Fin n) A) (β w : GL (Fin n) A) :
    w ∈ UJ σ (cT σ (β : Matrix (Fin n) (Fin n) A) * J * (β : Matrix (Fin n) (Fin n) A)) ↔ β * w * β⁻¹ ∈ UJ σ J := by
  have key : ∀ (J : Matrix (Fin n) (Fin n) A) (β w : GL (Fin n) A), w ∈ UJ σ J →
      β⁻¹ * w * β ∈ UJ σ (cT σ (β : Matrix (Fin n) (Fin n) A) * J * (β : Matrix (Fin n) (Fin n) A)) := fun J β w h => by
    show cT σ ((β⁻¹).1 * w.1 * β.1) * _ * ((β⁻¹).1 * w.1 * β.1) = _
    calc _ = cT σ β.1 * (cT σ w.1 * (cT σ (β.1 * (β⁻¹).1) * J * (β.1 * (β⁻¹).1)) * w.1) * β.1 := by
          simp only [cT_mul, Matrix.mul_assoc]
      _ = _ := by rw [Units.mul_inv, cT_one, Matrix.one_mul, Matrix.mul_one, show cT σ w.1 * J * w.1 = J from h]
  constructor
  · intro h
    have := key _ β⁻¹ w h
    rw [inv_inv] at this
    convert this using 2
    calc J = cT σ (β.1 * (β⁻¹).1) * J * (β.1 * (β⁻¹).1) := by rw [Units.mul_inv, cT_one, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [cT_mul, Matrix.mul_assoc]
  · intro h
    have := key J β _ h
    rwa [show β⁻¹ * (β * w * β⁻¹) * β = w by group] at this

theorem frGL_eq (I : AutInst) (β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) (x : GL (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)) :
    frGL β x = β * bc (Formalism.L2.Herm.intAf I.F I.E).subtype x * β⁻¹ := rfl

theorem frame_normaliser (I : AutInst) (g : ℕ) (hg : g ≠ 1) {ρ κ : ℕ} (hn : I.n = 2 * ρ + κ + 1) (hρ : 1 ≤ ρ) (hκ : 2 ≤ κ)
    (β : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) (hβ : IsFrame β I.L)
    (Z : PlaceSys (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (Formalism.L2.Herm.intAf I.F I.E) (Pl I.E) (fun Q => kP Q) (fun Q => resS I.F Q))
    (Pg : Finset (Pl I.E)) (hdiv : ∀ PP ∈ Pg, (g : 𝓞 I.E) ∈ PP.asIdeal)
    (hT : ∀ Q ∈ Pg, ∀ Q' ∈ Pg, sigA I (Z.e Q) ≠ Z.e Q')
    (hun : ∀ Q, sigA I (Z.e Q) = Z.e Q → ∃ δ : Formalism.L2.Herm.intAf I.F I.E, resS I.F Q (δ - sigInt I δ) ≠ 0)
    (ψ : ∀ PP : Pl I.E, AddChar (kP PP) ℂ) (hψ : ∀ Q ∈ Pg, ψ Q ≠ 1) (a : ∀ PP : Pl I.E, Fin I.n → Fin I.n → kP PP)
    (ha : ∀ PP ∈ Pg, ∀ i j, symEdge ρ κ i j → a PP i j ≠ 0) (K : Set I.Gf) (χ : I.Gf → ℂ)
    (hK : ∀ x : I.Gf, (x ∈ K ↔ (x : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) ∈ St β ∧
          ∀ PP ∈ Pg, redFn β PP x ∈ unipSym (kP PP) I.n ρ κ) ∧
        (x ∈ K → χ x = ∏ PP ∈ Pg, ψ PP (edgeVal ρ κ (a PP) (redFn β PP x))))
    (y : I.Gf) (hy : ∀ x, (x ∈ K ↔ y * x * y⁻¹ ∈ K) ∧ (x ∈ K → χ (y * x * y⁻¹) = χ x)) :
    ∃ z ∈ Subgroup.center I.Gf, ∃ c : Formalism.L2.Herm.intAf I.F I.E, c * sigInt I c = 1 ∧
      (∀ N : ℕ, Nat.Coprime N g → ZMod' I N (1 - c.1)) ∧
      ∀ (d : I.Gf) (x : GL (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)),
        frGL β x = (d : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) →
        (∀ i j, ZMod' I g (((x : Matrix (Fin I.n) (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)) - midDiag I.n ρ κ 1 c) i j).1) →
        d⁻¹ * (z⁻¹ * y) ∈ K := by
  obtain ⟨G, hG⟩ := GlobalTheory.T.unitary_group_conjugate_transpose_matrix I β hβ
  have hσ := sigA_sigA I
  have hS : ∀ s ∈ Formalism.L2.Herm.intAf I.F I.E, sigA I s ∈ Formalism.L2.Herm.intAf I.F I.E := fun s hs => sigA_mem I hs
  have hJ : cT (sigA I) (I.J.map (inclE (F := I.F) (Formalism.MainNotions.S.Af I.F))) = I.J.map (inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) := by
    ext i j
    exact (sigA_inclE I _).trans (congrArg _ (congrFun (congrFun I.J_herm i) j))
  have hcc : ∀ M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), cT (sigA I) (cT (sigA I) M) = M := fun M => by
    ext i j
    exact hσ _
  have hU : ∀ w, w ∈ UJ (sigA I) ((bc (Formalism.L2.Herm.intAf I.F I.E).subtype G).1) ↔ β * w * β⁻¹ ∈ UPts I.cm.sig I.J (Formalism.MainNotions.S.Af I.F) :=
    fun w => by rw [hG]; exact mem_UJ_conj _ _ _ _
  have keeps : ∀ y : I.Gf, (∀ x ∈ K, y * x * y⁻¹ ∈ K ∧ χ (y * x * y⁻¹) = χ x) →
      Keeps (fun Q : Pl I.E => resS I.F Q) (sigA I) ρ κ G Pg ψ a (β⁻¹ * y.1 * β) := by
    intro y hy x hx
    let X : I.Gf := ⟨frGL β x, (hU _).1 hx.1⟩
    have hX : X ∈ K := (hK X).1.2 ⟨⟨x, rfl⟩, fun PP hPP => by
      show redFn β PP (frGL β x) ∈ _
      rw [redFn_frGL]; exact hx.2 PP hPP⟩
    obtain ⟨h1, h2⟩ := hy X hX
    obtain ⟨⟨x', hx'⟩, h3⟩ := (hK _).1.1 h1
    rw [(hK _).2 h1, (hK _).2 hX, ← hx'] at h2
    rw [← hx'] at h3
    refine ⟨x', ?_, ⟨(hU _).2 (by rw [← frGL_eq, hx']; exact (y * X * y⁻¹).2), fun PP hPP => ?_⟩, ?_⟩
    · have e : β * bc (Formalism.L2.Herm.intAf I.F I.E).subtype x' * β⁻¹ =
        y.1 * (β * bc (Formalism.L2.Herm.intAf I.F I.E).subtype x * β⁻¹) * y.1⁻¹ := hx'
      calc _ = β⁻¹ * (β * bc (Formalism.L2.Herm.intAf I.F I.E).subtype x' * β⁻¹) * β := by group
        _ = _ := by rw [e]; group
    · have := h3 PP hPP
      rwa [redFn_frGL] at this
    · simp only [X, redFn_frGL] at h2
      exact h2
  obtain ⟨z, c, x₁, hz, hc, hsup, hm, hred⟩ := normaliser_core Z hσ hS hn hρ hκ
    (by rw [hG, cT_mul, cT_mul, hcc, hJ, Matrix.mul_assoc]) hT hun hψ ha (m := β⁻¹ * y.1 * β)
    ((hU _).2 (by rw [show β * (β⁻¹ * y.1 * β) * β⁻¹ = y.1 by group]; exact y.2))
    (keeps y fun x hx => ⟨(hy x).1.1 hx, (hy x).2 hx⟩)
    (by
      have := keeps y⁻¹ fun x hx => by
        have e : y * (y⁻¹ * x * y⁻¹⁻¹) * y⁻¹ = x := by group
        have h1 : y⁻¹ * x * y⁻¹⁻¹ ∈ K := (hy _).1.2 (by rw [e]; exact hx)
        exact ⟨h1, by rw [← (hy _).2 h1, e]⟩
      rwa [show β⁻¹ * (y⁻¹).1 * β = (β⁻¹ * y.1 * β)⁻¹ by rw [Subgroup.coe_inv]; group] at this)
  have hz' : sigA I z * z = 1 := by rw [mul_comm, hz]
  let zG : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) := ⟨z • 1, sigA I z • 1,
    by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hz, Matrix.one_mul, one_smul],
    by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hz', Matrix.one_mul, one_smul]⟩
  have hzc : ∀ w, zG * w = w * zG := fun w => Units.ext (by
    show z • 1 * w.1 = w.1 * z • 1
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one])
  have hzU : zG ∈ UPts I.cm.sig I.J (Formalism.MainNotions.S.Af I.F) := by
    have e : cT (sigA I) (z • (1 : Matrix (Fin I.n) (Fin I.n) _)) = sigA I z • 1 := by
      ext i j
      simp only [cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, map_mul, eq_comm (a := i)]
      split_ifs <;> simp
    show cT (sigA I) (z • 1) * _ * (z • 1) = _
    rw [e, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, hz, one_smul]
  have hm' : β⁻¹ * y.1 * β = zG * bc (Formalism.L2.Herm.intAf I.F I.E).subtype x₁ := Units.ext (by
    rw [hm]
    show _ = z • 1 * _
    rw [Matrix.smul_mul, Matrix.one_mul])
  have hpg : ∀ PP ∈ Pg, (g : kP PP) = 0 := fun PP hPP => by
    rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hdiv PP hPP)
  refine ⟨⟨zG, hzU⟩, Subgroup.mem_center_iff.2 fun w => Subtype.ext (hzc _).symm, c, Subtype.ext hc, fun N hN => ?_,
    fun d x hx hd => ?_⟩
  · have hN' : ∀ Q ∈ Pg, (N : kP Q) ≠ 0 := fun Q hQ h0 => by
      obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.2 hN).intCast (R := kP Q)
      rw [Int.cast_natCast, Int.cast_natCast, h0, hpg Q hQ, mul_zero, mul_zero, add_zero] at huv
      exact zero_ne_one huv
    have hN0 : (N : I.F) ≠ 0 := Nat.cast_ne_zero.2 fun e => hg (by rwa [e, Nat.coprime_zero_left] at hN)
    let b : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F := algebraMap I.F _ (N : I.F)⁻¹
    have hb : (N : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * b = 1 := by
      rw [← map_natCast (algebraMap I.F (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)), ← map_mul, mul_inv_cancel₀ hN0, map_one]
    have hb' : (N : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * sigA I b = 1 := by
      simpa using congrArg (sigA I) hb
    have key : ∀ b', (N : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * b' = 1 → ∀ Q ∈ Pg, Z.p Q b' ∈ Z.O Q := fun b' h Q hQ => by
      have h1 := (Z.r_ker Q N).not.1 (by rw [map_natCast]; exact hN' Q hQ)
      have h2 := congrArg (fun t => (Z.O Q).valuation (Z.p Q t)) h
      simp only [map_mul, map_one] at h2
      rw [← ValuationSubring.valuation_le_one_iff, ← h2]
      exact le_mul_of_one_le_left' (not_lt.1 h1)
    refine ⟨_, hsup b fun Q hQ => ⟨key b hb Q hQ, key _ hb' Q hQ⟩, ?_⟩
    rw [mul_left_comm, hb, mul_one]
  · have e : ((d⁻¹ * ((⟨zG, hzU⟩ : I.Gf)⁻¹ * y) : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) = frGL β (x⁻¹ * x₁) := by
      show d.1⁻¹ * (zG⁻¹ * y.1) = _
      rw [map_mul, map_inv, hx, frGL_eq]
      congr 1
      calc _ = zG⁻¹ * β * (β⁻¹ * y.1 * β) * β⁻¹ := by group
        _ = zG⁻¹ * (β * zG) * bc (Formalism.L2.Herm.intAf I.F I.E).subtype x₁ * β⁻¹ := by rw [hm']; group
        _ = _ := by rw [← hzc]; group
    refine (hK _).1.2 ⟨⟨_, e.symm⟩, fun PP hPP => ?_⟩
    obtain ⟨h, hh, e2⟩ := hred PP hPP
    have e3 : (bc (resS I.F PP) x).1 = midDiag I.n ρ κ 1 (resS I.F PP c) := by
      ext i j
      have := map_eq_zero_of_zmod I (resS I.F PP) (hpg PP hPP) (hd i j)
      rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
      refine this.trans ?_
      simp only [midDiag, Matrix.diagonal_apply]
      split_ifs <;> simp
    have e4 : bc (resS I.F PP) x₁ = bc (resS I.F PP) x * h := Units.ext (by rw [Units.val_mul, e3]; exact e2)
    rw [e, redFn_frGL, map_mul, map_inv, e4, inv_mul_cancel_left]
    exact hh

theorem sigInt_oToS (I : AutInst) {c c' : 𝓞 I.E} (h : (c' : I.E) = star (c : I.E)) :
    sigInt I (oToS I.F I.E c) = oToS I.F I.E c' :=
  Subtype.ext ((sigA_inclE I _).trans (congrArg (inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)) h.symm))

theorem conj_of_idem (I : AutInst)
    (Z : PlaceSys (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) (Formalism.L2.Herm.intAf I.F I.E) (Pl I.E) (fun Q => kP Q) (fun Q => resS I.F Q))
    {Q Q' : Pl I.E} (h : sigA I (Z.e Q) = Z.e Q') : ∀ c ∈ Q.asIdeal, ∃ c' ∈ Q'.asIdeal, (c' : I.E) = star (c : I.E) := by
  intro c hc
  obtain ⟨c', hc'⟩ := star_intOE I (a := (c : I.E)) ⟨c, rfl⟩
  refine ⟨c', ?_, hc'⟩
  have h1 : resS I.F Q' (sigInt I (oToS I.F I.E c)) = 0 :=
    Z.r_conj (σ := sigA I) (sigA_sigA I) (fun s hs => sigA_mem I hs) h (oToS I.F I.E c)
      ((resS_oToS Q c).trans (Ideal.Quotient.eq_zero_iff_mem.2 hc))
  rw [sigInt_oToS I hc', resS_oToS] at h1
  exact Ideal.Quotient.eq_zero_iff_mem.1 h1

theorem exists_res_ne (I : AutInst) (Q : Pl I.E) (h : ∃ δ δ' : 𝓞 I.E, (δ' : I.E) = star (δ : I.E) ∧ δ - δ' ∉ Q.asIdeal) :
    ∃ δ : Formalism.L2.Herm.intAf I.F I.E, resS I.F Q (δ - sigInt I δ) ≠ 0 := by
  obtain ⟨δ, δ', h1, h2⟩ := h
  refine ⟨oToS I.F I.E δ, fun h0 => h2 ?_⟩
  rw [sigInt_oToS I h1, ← map_sub, resS_oToS] at h0
  exact Ideal.Quotient.eq_zero_iff_mem.1 h0

theorem inst_normaliser (D : D7) (hρ : 1 ≤ D.R.rS) (I : AutInst) (hI : I = instOf D) (g : ℕ) (hg' : g = D.host.g 0 * D.host.g 1)
    (e0 f0 : Fin D.R.rS → VA I) (z0 : VA I) (bw bwd : Fin D.R.k → VA I) (ew : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)
    (hF : IsRefFrame I g e0 f0 z0 bw bwd ew) (hn : I.n = D.R.r) (psiEf : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F → ℂ)
    (hadd : ∀ x y, psiEf (x + y) = psiEf x * psiEf y) (hint : ∀ x ∈ IntAf I.F I.E, psiEf x = 1)
    (hrat : ∀ x : I.E, psiEf (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) x) * psiEinf I x = 1) (y : I.Gf)
    (hy : ∀ x, (x ∈ K2set I g e0 z0 bw ↔ y * x * y⁻¹ ∈ K2set I g e0 z0 bw) ∧ (x ∈ K2set I g e0 z0 bw →
      star (chi2f I psiEf g e0 f0 z0 bw bwd (y * x * y⁻¹)) = star (chi2f I psiEf g e0 f0 z0 bw bwd x))) :
    ∃ β, IsLiftFrame I g (flagVec e0 f0 z0 bw bwd) β ∧
      ∃ z ∈ Subgroup.center I.Gf, ∃ c : Formalism.L2.Herm.intAf I.F I.E, c * sigInt I c = 1 ∧
      (∀ N : ℕ, Nat.Coprime N g → ZMod' I N (1 - c.1)) ∧
      ∀ (d : I.Gf) (x : GL (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)),
        frGL β x = (d : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) →
        (∀ i j, ZMod' I g (((x : Matrix (Fin I.n) (Fin I.n) (Formalism.L2.Herm.intAf I.F I.E)) - midDiag I.n D.R.rS D.R.k 1 c) i j).1) →
        d⁻¹ * (z⁻¹ * y) ∈ K2set I g e0 z0 bw := by
  subst hI hg'
  obtain ⟨Pg, hPg⟩ := GlobalTheory.Core.Mi.PinModel.exists_isTypePlaces (D := D)
  have hnc := GlobalTheory.T.genus_type_places_pairwise_not_conjugate D Pg hPg
  have key : ∀ PP : Pl D.host.E, ∃ ψ : AddChar (kP PP) ℂ, ψ ≠ 1 := fun PP => by
    obtain ⟨ψ, hψ⟩ := (AddChar.exists_apply_ne_zero (α := kP PP) (a := 1)).2 one_ne_zero
    exact ⟨ψ, fun h => hψ (by rw [h]; rfl)⟩
  choose ψ0 hψ0 using key
  have hψ : IsGenericPsi Pg ψ0 := fun PP _ => hψ0 PP
  have hg : D.host.g 0 * D.host.g 1 ≠ 0 := mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  have hg1 : D.host.g 0 * D.host.g 1 ≠ 1 := fun e => (D.host.g_prime 0).ne_one (Nat.eq_one_of_mul_eq_one_right e)
  have hn' : (instOf D).n = 2 * D.R.rS + D.R.k + 1 := by
    rw [hn]
    obtain ⟨c, hc⟩ := D.R.m_even
    have := D.R.two_le_m
    unfold Ranks.r Ranks.rS
    omega
  have hk : 2 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  obtain ⟨hs1, hs2⟩ := GlobalTheory.T.flagVec_mem_Lf_and_inMod (instOf D) _ e0 f0 z0 bw bwd ew hF hn'
  obtain ⟨β₀, hβ₀⟩ := GlobalTheory.T.exists_latticeFrame_lifting_spanning_vectors_mod D _ hg _ hs1 hs2
  have hN : ∀ s : Formalism.L2.Herm.intAf D.host.F D.host.E,
      (∀ PP ∈ Pg, resS D.host.F PP s = 0 ∧ resS D.host.F PP (sigInt (instOf D) s) = 0) →
      ZMod' (instOf D) (D.host.g 0 * D.host.g 1) s.1 := by
    intro s hs
    refine GlobalTheory.T.integralAdele_congr_zero_of_residues_squarefree (instOf D) _ hg (GlobalTheory.T.typePrimes_product_not_mem_sq_place D) s fun Q hQ => ?_
    obtain ⟨PP, hPP, rfl | h⟩ := GlobalTheory.T.typePrimePlace_mem_or_conj_genusTypePlaceSet D Pg hPg Q hQ
    · exact (hs _ hPP).1
    · exact (h s).2 (hs _ hPP).2
  obtain ⟨a₁, a₂, ha, hχ⟩ := GlobalTheory.T.character_residueFields_eq_prod_genericShift D.host.E (Formalism.L2.Herm.intAf D.host.F D.host.E) Pg (fun PP => resS D.host.F PP)
    (fun PP => (resS D.host.F PP).comp (sigInt (instOf D)))
    (fun s => star (psiEf (divN (instOf D) (D.host.g 0 * D.host.g 1) s.1))) ψ0 hψ
    (fun s t => (congrArg (fun z => star (psiEf z))
        (Formalism.L2.SG.Pf.unitaryCongruence.divN_add (instOf D) (D.host.g 0 * D.host.g 1) s.1 t.1)).trans (by rw [hadd, star_mul']))
    (fun s hs => by
      obtain ⟨t, ht, e⟩ := hN s hs
      have : divN (instOf D) (D.host.g 0 * D.host.g 1) s.1 = t :=
        (congrArg _ e).trans (Formalism.L2.SG.Pf.unitaryCongruence.divN_gmul _ _ hg t)
      show star (psiEf (divN (instOf D) (D.host.g 0 * D.host.g 1) s.1)) = 1
      rw [this, hint t ht, star_one])
    (GlobalTheory.T.exists_integralAdele_prescribed_residues_and_conj D Pg hnc)
    (GlobalTheory.T.residueSupport_single_place_to_conjugatePair_position D Pg hPg.1 hnc (fun s => star (psiEf (divN (instOf D) (D.host.g 0 * D.host.g 1) s.1)) ≠ 1) fun Q hQ => by
      obtain ⟨s, h1, h2⟩ := GlobalTheory.T.exists_finiteAdditiveChar_ne_one_at_each_prime D psiEf hadd hint hrat Q hQ
      exact ⟨s, h1, fun h => h2 (by simpa using congrArg star h)⟩)
  obtain ⟨a, ha1, hK⟩ := read_in_frame (instOf D) _ hg e0 f0 z0 bw bwd ew hF hn' β₀ hβ₀ Pg hPg.1 hN psiEf hadd hint ψ0 a₁ a₂ ha hχ
  exact ⟨β₀, hβ₀, frame_normaliser (instOf D) _ hg1 hn' hρ hk β₀ hβ₀.1 (adPlaces D) Pg hPg.1
    (fun Q hQ Q' hQ' h => hnc Q hQ Q' hQ' (conj_of_idem (instOf D) (adPlaces D) h))
    (fun Q h => exists_res_ne (instOf D) Q (GlobalTheory.T.exists_integer_sub_conj_notMem_self_conjugate_place D Q (conj_of_idem (instOf D) (adPlaces D) h))) ψ0 hψ a ha1 _
    (fun x => star (chi2f (instOf D) psiEf (D.host.g 0 * D.host.g 1) e0 f0 z0 bw bwd x)) hK y hy⟩


open Formalism.L2.SG.PoincareInHH.PoincareSetting in
theorem setting_normaliser {D : D7} (X : HidaSetting D) (h : X.B.I = instOf D) (hρ : 1 ≤ D.R.rS) (u : D.what₂.Word) (y : X.B.I.Gf)
    (hy : ∀ x, (x ∈ X.K2 ↔ y * x * y⁻¹ ∈ X.K2) ∧ (x ∈ X.K2 → star (X.chi2 (y * x * y⁻¹)) = star (X.chi2 x))) :
    ∃ z ∈ Subgroup.center X.B.I.Gf, ∃ w ∈ Hfin X u, (∀ w' ∈ Hfin X u, w * w' = w' * w) ∧
      ∃ k ∈ X.K2, y = (X.xu u)⁻¹ * w * X.xu u * z * k := by
  obtain ⟨β, hβ, z, hz, c, hc, hs, hd⟩ := inst_normaliser D hρ X.B.I h X.B.g X.g_eq X.e0 X.f0 X.z0 X.bw X.bwd X.ew
    (isRefFrame_setting X) X.n_eq X.psiEf X.psiEf_add X.psiEf_int X.psiEf_rat y hy
  obtain ⟨w, hw, hw', x, hx, hx'⟩ := GlobalTheory.T.scalar_complement_frame_diag_mod_conductor D X u β hβ c hc hs
  refine ⟨z, hz, w, hw, hw', _, hd _ x hx hx', ?_⟩
  rw [Subgroup.mem_center_iff.1 hz]
  group

end GlobalTheory.LevNorm

end
end

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.LevNorm

open Formalism.BasicNotions.TH

theorem embA_injective {D : D7} {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) :
    Function.Injective (embA d o) := fun _ _ h =>
  congrArg Prod.fst (o.emb_injective (d.wittDecomp_anisotropicEmbedding_injective h))

theorem finf_sand {D : D7} {k n : ℕ} (p : Mx D k n) (m : Mx D n n) (j : Mx D n k) (hm : m.map (CenAct.finf D) = 1)
    (h : p ⬝ j = 1) : (p ⬝ (m ⬝ j)).map (CenAct.finf D) = 1 := by
  rw [← Matrix.mul_assoc, CenAct.map_sand p m j hm, h, Matrix.map_one _ (map_zero _) (map_one _)]

theorem mem_GfC_of_embA {D : D7} {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) {a : GA D A}
    (h : embA d o a ∈ GfC S) : a ∈ GfC A := by
  rw [embA_apply, CenAct.mem_GfC_iff] at h
  have h1 := finf_sand d.p0 _ d.j0 h d.p0_j0
  rw [d.wittDecomp_anisotropicEmbedding_inclAnisotropic, cancel₂ d.p0_j0, Matrix.one_mul] at h1
  have h2 := finf_sand o.pA _ o.jA h1 o.pA_jA
  rw [o.emb_jA, cancel₂ o.pA_jA, Matrix.one_mul] at h2
  exact (CenAct.mem_GfC_iff _ _).2 h2

theorem matches_differ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (hρ : 1 ≤ D.R.rS)
    (u : D.what₂.Word) {ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ} {A : HSp D} (B : SBes X h u ψ A)
    {J : Set (GA D (D.sp.Y 0))} {χ : GA D (D.sp.Y 0) → ℂ} {t t' : GA D (D.sp.Y 0)} (ht : Matches X h J χ t) (ht' : Matches X h J χ t') :
    ∃ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) ∧ ∃ a ∈ GfC A, a ∈ Subgroup.center (GA D A) ∧ ∃ k ∈ J,
      t = ((iotaX X h).symm (1, X.xu u))⁻¹ * embA B.d B.o a * (iotaX X h).symm (1, X.xu u) * z * t' * k := by
  let j : X.B.I.Gf →* GA D (D.sp.Y 0) := ((iotaX X h).symm.toMulEquiv.toMonoidHom).comp (MonoidHom.inr _ _)
  have hj : ∀ x, iotaX X h (j x) = (1, x) := fun x => (iotaX X h).apply_symm_apply _
  have hjG : ∀ x, j x ∈ GfC (D.sp.Y 0) := fun x => (GlobalTheory.SeeConjRead.iotaX_fst_eq_one_iff X h _).1 (by rw [hj])
  have hjJ : ∀ x, j x ∈ rowJ X h ↔ x ∈ X.K2 := fun x => by
    show (iotaX X h (j x)).1 = 1 ∧ (iotaX X h (j x)).2 ∈ X.K2 ↔ _
    rw [hj]
    exact and_iff_right rfl
  have hjχ : ∀ x, rowChi X h (j x) = star (X.chi2 x) := fun x => by
    show star (X.chi2 (iotaX X h (j x)).2) = _
    rw [hj]
  obtain ⟨y, hy⟩ : ∃ y, j y = t * t'⁻¹ := ⟨_, GlobalTheory.SeeConjRead.eq_symm_one X h _
    ((GlobalTheory.SeeConjRead.iotaX_fst_eq_one_iff X h _).2 (mul_mem ht.1 (inv_mem ht'.1)))⟩
  have e1 : ∀ x, t'⁻¹⁻¹ * (t'⁻¹ * j x * t') * t'⁻¹ = j x := fun x => by group
  have e2 : ∀ x, t⁻¹⁻¹ * (t'⁻¹ * j x * t') * t⁻¹ = j (y * x * y⁻¹) := fun x => by
    rw [map_mul, map_mul, map_inv, hy]; group
  have hJ : ∀ x, t'⁻¹ * j x * t' ∈ J ↔ x ∈ X.K2 := fun x => by rw [(ht'.2 _).1, e1, hjJ]
  obtain ⟨z, hz, w, hw, hw', k, hk, e⟩ := setting_normaliser X h hρ u y fun x =>
    ⟨by rw [← hJ, (ht.2 _).1, e2, hjJ], fun hx => by
      rw [← hjχ, ← hjχ, ← e2, (ht.2 _).2 ((hJ x).2 hx), ← (ht'.2 _).2 ((hJ x).2 hx), e1]⟩
  obtain ⟨a, ha⟩ := (B.tieH (j w)).2 (by rw [hj]; exact ⟨one_mem _, hw⟩)
  refine ⟨j z, hjG z, Subgroup.mem_center_iff.2 fun g => (iotaX X h).injective ?_, a,
    mem_GfC_of_embA B.d B.o (ha ▸ hjG w), Subgroup.mem_center_iff.2 fun b => embA_injective B.d B.o ((iotaX X h).injective ?_),
    t'⁻¹ * j k * t', (hJ k).2 hk, ?_⟩
  · rw [map_mul, map_mul, hj]
    exact Prod.ext (by simp) (Subgroup.mem_center_iff.1 hz _)
  · rw [map_mul, map_mul, map_mul, map_mul, ha, hj]
    exact Prod.ext (by simp) (hw' _ ((B.tieH _).1 ⟨b, rfl⟩).2).symm
  · show t = (j (X.xu u))⁻¹ * embA B.d B.o a * j (X.xu u) * j z * t' * (t'⁻¹ * j k * t')
    rw [ha]
    have e3 := congrArg j e
    rw [hy, map_mul, map_mul, map_mul, map_mul, map_inv] at e3
    calc t = t * t'⁻¹ * t' := by group
      _ = _ := by rw [e3]; group

end GlobalTheory.LevNorm

end
