module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLevelRepresentable
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLevelRepresentable
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.CechRep

variable {V W : Scheme.{0}} (f : V ⟶ W)

def IsPow (n : ℕ) (Z : Scheme.{0}) (p : Fin (n + 1) → (Z ⟶ V)) : Prop :=
  (∀ i, p i ≫ f = p 0 ≫ f) ∧ ∀ (U : Scheme.{0}) (y : Fin (n + 1) → (U ⟶ V)), (∀ i, y i ≫ f = y 0 ≫ f) →
    ∃! g : U ⟶ Z, ∀ i, g ≫ p i = y i

theorem exists_pow (P : MorphismProperty Scheme.{0}) [P.IsStableUnderBaseChange] [P.IsMultiplicative]
    (hf : P f) (n : ℕ) : ∃ (Z : Scheme.{0}) (p : Fin (n + 1) → (Z ⟶ V)), IsPow f n Z p ∧ P (p 0) := by
  induction n with
  | zero =>
    refine ⟨V, fun _ => 𝟙 V, ⟨fun _ => rfl, fun U y _ => ⟨y 0, fun i => ?_, fun g hg => ?_⟩⟩, P.id_mem V⟩
    · rw [Fin.fin_one_eq_zero i]; simp
    · simpa using hg 0
  | succ n ih =>
    obtain ⟨Z, p, ⟨hc, hu⟩, hP⟩ := ih
    let q : Fin (n + 2) → (pullback (p 0 ≫ f) f ⟶ V) :=
      Fin.snoc (α := fun _ => pullback (p 0 ≫ f) f ⟶ V) (fun j => pullback.fst _ _ ≫ p j) (pullback.snd _ _)
    have qc : ∀ j : Fin (n + 1), q j.castSucc = pullback.fst _ _ ≫ p j := fun j => by simp [q]
    have ql : q (Fin.last _) = pullback.snd _ _ := by simp [q]
    have hz : (Fin.castSucc (0 : Fin (n + 1)) : Fin (n + 2)) = 0 := rfl
    have q0 : q 0 = pullback.fst _ _ ≫ p 0 := qc 0
    refine ⟨pullback (p 0 ≫ f) f, q, ⟨fun i => ?_, fun U y hy => ?_⟩, ?_⟩
    · rw [q0]
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [ql, ← pullback.condition, Category.assoc]
      · rw [qc, Category.assoc, Category.assoc, hc j]
    · have h' : ∀ j : Fin (n + 1), y j.castSucc ≫ f = y (Fin.castSucc 0) ≫ f := fun j => by
        rw [hy, hz, hy]
      obtain ⟨g0, hg0, hg0u⟩ := hu U (fun j => y j.castSucc) h'
      have hw : g0 ≫ p 0 ≫ f = y (Fin.last _) ≫ f := by
        rw [← Category.assoc, hg0 0, hy (Fin.last _), hz]
      refine ⟨pullback.lift g0 (y (Fin.last _)) hw, fun i => ?_, fun g hg => ?_⟩
      · refine Fin.lastCases ?_ (fun j => ?_) i
        · rw [ql, pullback.lift_snd]
        · rw [qc, pullback.lift_fst_assoc, hg0 j]
      · apply pullback.hom_ext
        · rw [pullback.lift_fst]
          refine hg0u _ (fun j => ?_)
          rw [Category.assoc, ← qc, hg]
        · rw [pullback.lift_snd, ← ql, hg]
    · rw [q0]
      exact P.comp_mem _ _ (P.pullback_fst _ _ hf) hP

end GlobalTheory.EtC.CechRep

namespace GlobalTheory.EtC.CechRep

variable {V W : Scheme.{0}} (f : V ⟶ W)

noncomputable section

def isLimitPow {n : ℕ} {Z : Scheme.{0}} {p : Fin (n + 1) → (Z ⟶ V)} (h : IsPow f n Z p) :
    IsLimit (WidePullbackShape.mkCone (F := WidePullbackShape.wideCospan W (fun _ : Fin (n + 1) => V) (fun _ => f))
      (p 0 ≫ f) p (fun j => h.1 j)) := by
  have hs : ∀ s : Cone (WidePullbackShape.wideCospan W (fun _ : Fin (n + 1) => V) (fun _ => f)),
      ∀ j, s.π.app (some j) ≫ f = s.π.app (some 0) ≫ f := fun s j => by
    have a : s.π.app (some j) ≫ f = s.π.app none := s.w (WidePullbackShape.Hom.term j)
    have b : s.π.app (some 0) ≫ f = s.π.app none := s.w (WidePullbackShape.Hom.term 0)
    rw [a, b]
  refine IsLimit.mk (fun s => (h.2 s.pt (fun j => s.π.app (some j)) (hs s)).exists.choose) (fun s j => ?_)
    (fun s m hm => ?_)
  · have hl := (h.2 s.pt (fun j => s.π.app (some j)) (hs s)).exists.choose_spec
    cases j with
    | none =>
      have b : s.π.app (some 0) ≫ f = s.π.app none := s.w (WidePullbackShape.Hom.term 0)
      change (h.2 s.pt (fun j => s.π.app (some j)) (hs s)).exists.choose ≫ (p 0 ≫ f) = s.π.app none
      rw [← Category.assoc, hl 0]
      exact b
    | some j =>
      exact hl j
  · exact (h.2 s.pt (fun j => s.π.app (some j)) (hs s)).unique (fun j => hm (some j))
      (h.2 s.pt (fun j => s.π.app (some j)) (hs s)).exists.choose_spec

end

end GlobalTheory.EtC.CechRep

theorem GlobalTheory.EtC.cech_level_representable : ∀ (P : MorphismProperty Scheme.{0}) [P.IsStableUnderBaseChange] [P.IsMultiplicative] (V W : Scheme.{0}) (f : V ⟶ W), P f → ∀ k : SimplexCategoryᵒᵖ, ∃ (Z : Scheme.{0}) (π : Z ⟶ V) (e : yoneda.obj Z ≅ (cech f).obj k), P π ∧ e.hom ≫ (cechAug f).app k = yoneda.map (π ≫ f) := by
  intro P _ _ V W f hf k
  obtain ⟨Z, p, h, hP⟩ := GlobalTheory.EtC.CechRep.exists_pow f P hf k.unop.len
  have hY := isLimitOfPreserves yoneda (GlobalTheory.EtC.CechRep.isLimitPow f h)
  let D := WidePullbackShape.wideCospan (yoneda.obj W) (fun _ : Fin (k.unop.len + 1) => yoneda.obj V)
    (fun _ => yoneda.map f)
  let iso : WidePullbackShape.wideCospan W (fun _ : Fin (k.unop.len + 1) => V) (fun _ => f) ⋙ yoneda ≅ D :=
    WidePullbackShape.diagramIsoWideCospan _
  have hL := (IsLimit.postcomposeHomEquiv iso _).symm hY
  refine ⟨Z, p 0, IsLimit.conePointUniqueUpToIso hL (limit.isLimit D), hP, ?_⟩
  have := IsLimit.conePointUniqueUpToIso_hom_comp hL (limit.isLimit D) none
  change _ ≫ limit.π D none = _
  refine this.trans ?_
  change yoneda.map (p 0 ≫ f) ≫ iso.hom.app none = _
  simp [iso, WidePullbackShape.diagramIsoWideCospan]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLevelRepresentableStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_representable_cech_level_of_stable : ∀ (P : MorphismProperty Scheme.{0}) [P.IsStableUnderBaseChange] [P.IsMultiplicative] (V W : Scheme.{0}) (f : V ⟶ W), P f → ∀ k : SimplexCategoryᵒᵖ, ∃ (Z : Scheme.{0}) (π : Z ⟶ V) (e : yoneda.obj Z ≅ (cech f).obj k), P π ∧ e.hom ≫ (cechAug f).app k = yoneda.map (π ≫ f) := by
  first | (exact @GlobalTheory.EtC.cech_level_representable) | (exact GlobalTheory.EtC.cech_level_representable) | (intros; apply GlobalTheory.EtC.cech_level_representable  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgClosedFractionRingOfMonicPolynomialsHaveRoo
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgClosedFractionRing
open Polynomial

namespace GlobalTheory.FractionRingRootRange

theorem root_mem_range {A B : Type} [CommRing A] [Nontrivial A] [CommRing B] [IsDomain B] [Algebra A B]
    (h : GlobalTheory.EtC.AIC A) (z : B) :
    ∀ (n : ℕ) (p : A[X]), p.natDegree = n → p.Monic → aeval z p = 0 → ∃ a : A, algebraMap A B a = z := by
  intro n
  induction n with
  | zero =>
    intro p hdeg hmon hz
    rw [Polynomial.eq_one_of_monic_natDegree_zero hmon hdeg, map_one] at hz
    exact absurd hz one_ne_zero
  | succ n ih =>
    intro p hdeg hmon hz
    obtain ⟨a, ha⟩ := h p hmon (by omega)
    have hmul : (X - C a) * (p /ₘ (X - C a)) = p := mul_divByMonic_eq_iff_isRoot.mpr ha
    have hqmon : (p /ₘ (X - C a)).Monic :=
      (monic_X_sub_C a).of_mul_monic_left (by rw [hmul]; exact hmon)
    have hqdeg : (p /ₘ (X - C a)).natDegree = n := by
      rw [natDegree_divByMonic p (monic_X_sub_C a), natDegree_X_sub_C, hdeg]
      omega
    rw [← hmul, map_mul] at hz
    simp only [map_sub, aeval_X, aeval_C] at hz
    rcases mul_eq_zero.mp hz with h1 | h1
    · exact ⟨a, (sub_eq_zero.mp h1).symm⟩
    · exact ih _ hqdeg hqmon h1

theorem isAlgClosed_fractionRing (A : Type) [CommRing A] [IsDomain A] (h : GlobalTheory.EtC.AIC A) :
    IsAlgClosed (FractionRing A) := by
  refine IsAlgClosed.of_exists_root _ fun p hmon hirr => ?_
  have hdeg : p.degree ≠ 0 := (Polynomial.degree_pos_of_irreducible hirr).ne'
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (p.map (algebraMap (FractionRing A) (AlgebraicClosure (FractionRing A))))
    (by rwa [degree_map])
  have hpz : aeval z p = 0 := by
    rw [aeval_def, ← eval_map]
    exact hz
  obtain ⟨b, hbM, hb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors A) p
  have hbK : algebraMap A (FractionRing A) b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hbM
  have hq0 : IsLocalization.integerNormalization (nonZeroDivisors A) p ≠ 0 := by
    intro h0
    have h1 := congrArg (fun r => r.coeff p.natDegree) hb
    simp only [h0, Polynomial.map_zero, coeff_zero] at h1
    rw [Algebra.smul_def] at h1
    change 0 = (C (algebraMap A (FractionRing A) b) * p).coeff p.natDegree at h1
    rw [coeff_C_mul, hmon.coeff_natDegree, mul_one] at h1
    exact hbK h1.symm
  have hqz : aeval z (IsLocalization.integerNormalization (nonZeroDivisors A) p) = 0 := by
    rw [← aeval_map_algebraMap (FractionRing A), hb, Algebra.smul_def, map_mul, hpz, mul_zero]
  have inj : ∀ x : A, algebraMap A (AlgebraicClosure (FractionRing A)) x = 0 → x = 0 := by
    intro x hx
    rw [IsScalarTower.algebraMap_apply A (FractionRing A), map_eq_zero] at hx
    exact IsFractionRing.to_map_eq_zero_iff.mp hx
  have hw := integralNormalization_aeval_eq_zero hqz inj
  have hmon' : (integralNormalization (IsLocalization.integerNormalization (nonZeroDivisors A) p)).Monic := by
    exact monic_integralNormalization hq0
  obtain ⟨a, ha⟩ := root_mem_range (B := AlgebraicClosure (FractionRing A)) h _ _ _ rfl hmon' hw
  set c := (IsLocalization.integerNormalization (nonZeroDivisors A) p).leadingCoeff
  have hc : algebraMap A (FractionRing A) c ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]
    exact leadingCoeff_ne_zero.mpr hq0
  have ha' : algebraMap A (AlgebraicClosure (FractionRing A)) a =
      algebraMap A (AlgebraicClosure (FractionRing A)) c * z := by
    rw [ha]
  refine ⟨algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) c, ?_⟩
  have hcB : algebraMap (FractionRing A) (AlgebraicClosure (FractionRing A)) (algebraMap A (FractionRing A) c) ≠ 0 :=
    (_root_.map_ne_zero _).mpr hc
  have hx : algebraMap (FractionRing A) (AlgebraicClosure (FractionRing A))
      (algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) c) = z := by
    rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, ha']
    rw [← IsScalarTower.algebraMap_apply] at hcB
    field_simp
  apply (algebraMap (FractionRing A) (AlgebraicClosure (FractionRing A))).injective
  rw [map_zero, ← eval₂_hom, ← eval_map, hx]
  exact hz

end GlobalTheory.FractionRingRootRange
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgClosedFractionRingOfMonicPolynomialsHaveRoo
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory

open Polynomial

theorem isAlgClosed_fractionRing_of_AIC : ∀ (A : Type) [CommRing A] [IsDomain A], AIC A → IsAlgClosed (FractionRing A) := by
  first
  | exact @_root_.GlobalTheory.FractionRingRootRange.isAlgClosed_fractionRing
  | exact _root_.GlobalTheory.FractionRingRootRange.isAlgClosed_fractionRing
  | (apply _root_.GlobalTheory.FractionRingRootRange.isAlgClosed_fractionRing <;> assumption)
  | (intros; apply _root_.GlobalTheory.FractionRingRootRange.isAlgClosed_fractionRing <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FractionRingRootRange.isAlgClosed_fractionRing <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FractionRingRootRange.isAlgClosed_fractionRing ..)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgClosedFractionRingOfMonicPolynomialsHaveRooStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAlgClosed_fractionRing_of_monic_polynomials_have_roots : ∀ (A : Type) [CommRing A] [IsDomain A], AIC A → IsAlgClosed (FractionRing A) := by
  first | (exact @GlobalTheory.isAlgClosed_fractionRing_of_AIC) | (exact GlobalTheory.isAlgClosed_fractionRing_of_AIC) | (intros; apply GlobalTheory.isAlgClosed_fractionRing_of_AIC  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplicialCochainClassesBasicProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplicialCochainClassesBasicProperties
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.ClsBasic

variable {R : Type} [CommRing R]

theorem single_add' {C : Type*} [Category C] [Preadditive C] {K L : CochainComplex C ℤ} {p q : ℤ}
    (f g : K.X p ⟶ L.X q) (n : ℤ) : Cochain.single (f + g) n = Cochain.single f n + Cochain.single g n := by
  ext p' q' h
  by_cases hp : p' = p
  · subst hp
    by_cases hq : q' = q
    · subst hq; simp
    · simp [Cochain.single_v_eq_zero' _ _ _ _ _ hq]
  · simp [Cochain.single_v_eq_zero _ _ _ _ _ hp]

theorem ofHom_comp_single {C : Type*} [Category C] [Preadditive C] {K K' L : CochainComplex C ℤ} {p q : ℤ}
    (g : K' ⟶ K) (f : K.X p ⟶ L.X q) (n : ℤ) :
    (Cochain.ofHom g).comp (Cochain.single f n) (zero_add n) = Cochain.single (g.f p ≫ f) n := by
  ext p' q' h
  rw [Cochain.comp_v _ _ (zero_add n) p' p' q' (add_zero p') h, Cochain.ofHom_v]
  by_cases hp : p' = p
  · subst hp
    by_cases hq : q' = q
    · subst hq; simp
    · simp [Cochain.single_v_eq_zero' _ _ _ _ _ hq]
  · simp [Cochain.single_v_eq_zero _ _ _ _ _ hp]

theorem resι_d (F : Shv R) : resι R F ≫ (res R F).d 0 1 = 0 := by
  have h := (injectiveResolution F).ι'.comm 0 1
  have h0 : ((singleFunctor (Shv R) 0).obj F).d 0 1 = 0 := by simp
  rw [h0, zero_comp] at h
  change ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫ (injectiveResolution F).ι'.f 0) ≫ (injectiveResolution F).cochainComplex.d 0 1 = 0
  erw [Category.assoc, h]
  rfl

theorem chains_d (E : Spc) (n : ℕ) :
    ((chains R).obj E).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) =
      (chainsXIso R E (n + 1)).hom ≫ (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i)) ≫
        (chainsXIso R E n).inv := by
  have h := HomologicalComplex.extend_d_eq ((chainsN R).obj E) ComplexShape.embeddingDownNat (i := n + 1) (j := n) rfl rfl
  have h2 : ((chainsN R).obj E).d (n + 1) n = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i) :=
    AlgebraicTopology.alternatingFaceMapComplex_obj_d _ n
  rw [← h2]
  exact h

theorem chainsXIso_nat {E E' : Spc} (f : E' ⟶ E) (n : ℕ) :
    ((chains R).map f).f (-(n : ℤ)) ≫ (chainsXIso R E n).hom = (chainsXIso R E' n).hom ≫ (free R).map (f.app (op ⦋n⦌)) := by
  have h := HomologicalComplex.extendMap_f ((chainsN R).map f) ComplexShape.embeddingDownNat (i := n) (i' := -(n : ℤ)) rfl
  change (HomologicalComplex.extendMap ((chainsN R).map f) ComplexShape.embeddingDownNat).f (-(n : ℤ)) ≫ _ = _
  rw [h]
  simp only [chainsXIso]
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

theorem δ_cls {E : Spc} {F : Shv R} {n : ℕ} (s : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F) :
    δ (n : ℤ) ((n + 1 : ℕ) : ℤ) (Cochain.single (p := -(n : ℤ)) (q := 0) ((chainsXIso R E n).hom ≫ s ≫ resι R F) n) =
      (((n + 1 : ℕ) : ℤ)).negOnePow • Cochain.single (p := -((n + 1 : ℕ) : ℤ)) (q := 0)
        ((chainsXIso R E (n + 1)).hom ≫ cobd s ≫ resι R F) ((n + 1 : ℕ) : ℤ) := by
  rw [Cochain.δ_single _ (n : ℤ) ((n + 1 : ℕ) : ℤ) (by push_cast; ring) (-((n + 1 : ℕ) : ℤ)) 1 (by push_cast; ring) rfl]
  rw [Category.assoc, Category.assoc, resι_d, comp_zero, comp_zero, Cochain.single_zero, zero_add]
  congr 2
  rw [chains_d, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc]
  congr 1
  rw [← Category.assoc]
  congr 1
  rw [cobd, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Preadditive.zsmul_comp]

end GlobalTheory.EtC.ClsBasic

open GlobalTheory.EtC.ClsBasic in
theorem GlobalTheory.EtC.isCls_basic : ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc) (n : ℕ),
    (∀ s : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F, cobd s = 0 → ∃ x : H R E F n, IsCls s x) ∧
    (∀ (s s' : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F) (x x' : H R E F n),
      IsCls s x → IsCls s' x' → IsCls (s + s') (x + x')) ∧
    (∀ (s : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F) (x x' : H R E F n),
      IsCls s x → IsCls s x' → x = x') ∧
    (∀ (t : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F) (x : H R E F ((n + 1 : ℕ) : ℤ)),
      IsCls (cobd t) x → x = 0) ∧
    ∀ (E' : Spc) (f : E' ⟶ E) (s : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F) (x : H R E F n),
      IsCls s x → IsCls ((free R).map (f.app (op ⦋n⦌)) ≫ s) (pull R f F n x) := by
  intro R _ F E n
  refine ⟨fun s hs => ?_, fun s s' x x' hx hx' => ?_, fun s x x' hx hx' => ?_, fun t x hx => ?_, fun E' f s x hx => ?_⟩
  · refine ⟨CohomologyClass.mk (Cocycle.mk (Cochain.single (p := -(n : ℤ)) (q := 0) ((chainsXIso R E n).hom ≫ s ≫ resι R F) n)
      ((n + 1 : ℕ) : ℤ) (by push_cast; ring) ?_), _, rfl, rfl⟩
    rw [ClsBasic.δ_cls, hs, zero_comp, comp_zero, Cochain.single_zero, smul_zero]
  · obtain ⟨z, rfl, hz⟩ := hx
    obtain ⟨z', rfl, hz'⟩ := hx'
    refine ⟨z + z', (CohomologyClass.mk_add z z').symm, ?_⟩
    change z.1 + z'.1 = _
    rw [hz, hz', ← ClsBasic.single_add', Preadditive.add_comp, Preadditive.comp_add]
  · obtain ⟨z, rfl, hz⟩ := hx
    obtain ⟨z', rfl, hz'⟩ := hx'
    have : z = z' := Cocycle.ext (hz.trans hz'.symm)
    rw [this]
  · obtain ⟨z, rfl, hz⟩ := hx
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n : ℤ) (by push_cast; ring)]
    refine ⟨(((n + 1 : ℕ) : ℤ)).negOnePow • Cochain.single (p := -(n : ℤ)) (q := 0) ((chainsXIso R E n).hom ≫ t ≫ resι R F) n, ?_⟩
    rw [δ_units_smul, ClsBasic.δ_cls, smul_smul, Int.units_mul_self, one_smul, hz]
  · obtain ⟨z, rfl, hz⟩ := hx
    refine ⟨zcomp (Cocycle.ofHom ((chains R).map f)) z (zero_add _), rfl, ?_⟩
    change (Cochain.ofHom ((chains R).map f)).comp z.1 (zero_add _) = _
    rw [hz, ClsBasic.ofHom_comp_single, ← Category.assoc, ClsBasic.chainsXIso_nat]
    simp only [Category.assoc]

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplicialCochainClassesBasicPropertiesStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simplicialCochain_classes_basic_properties :
    ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc) (n : ℕ),
    (∀ s : (free R).obj (E.obj (op (SimplexCategory.mk n))) ⟶ F,
      cobd s = 0 → ∃ x : H R E F n, IsCls s x) ∧
    (∀ (s s' : (free R).obj (E.obj (op (SimplexCategory.mk n))) ⟶ F) (x x' : H R E F n),
      IsCls s x → IsCls s' x' → IsCls (s + s') (x + x')) ∧
    (∀ (s : (free R).obj (E.obj (op (SimplexCategory.mk n))) ⟶ F) (x x' : H R E F n),
      IsCls s x → IsCls s x' → x = x') ∧
    (∀ (t : (free R).obj (E.obj (op (SimplexCategory.mk n))) ⟶ F) (x : H R E F ((n + 1 : ℕ) : ℤ)),
      IsCls (cobd t) x → x = 0) ∧
    ∀ (E' : Spc) (f : E' ⟶ E) (s : (free R).obj (E.obj (op (SimplexCategory.mk n))) ⟶ F) (x : H R E F n),
      IsCls s x → IsCls ((free R).map (f.app (op (SimplexCategory.mk n))) ≫ s) (pull R f F n x) := by
  intro R _ F E n
  have differential (s : (free R).obj (E.obj (op (SimplexCategory.mk n))) ⟶ F) :
      δ (n : ℤ) ((n + 1 : ℕ) : ℤ)
          (Cochain.single (p := -(n : ℤ)) (q := 0) ((chainsXIso R E n).hom ≫ s ≫ resι R F) n) =
        (((n + 1 : ℕ) : ℤ)).negOnePow • Cochain.single (p := -((n + 1 : ℕ) : ℤ)) (q := 0)
          ((chainsXIso R E (n + 1)).hom ≫ cobd s ≫ resι R F) ((n + 1 : ℕ) : ℤ) := by
    rw [Cochain.δ_single _ (n : ℤ) ((n + 1 : ℕ) : ℤ) (by push_cast; ring)
      (-((n + 1 : ℕ) : ℤ)) 1 (by push_cast; ring) rfl]
    rw [Category.assoc, Category.assoc, ClsBasic.resι_d, comp_zero, comp_zero, Cochain.single_zero, zero_add]
    congr 2
    rw [ClsBasic.chains_d, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc]
    congr 1
    rw [← Category.assoc]
    congr 1
    rw [cobd, Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Preadditive.zsmul_comp]
  refine ⟨fun s hs => ?_, fun s s' x x' hx hx' => ?_, fun s x x' hx hx' => ?_,
    fun t x hx => ?_, fun E' f s x hx => ?_⟩
  · refine ⟨CohomologyClass.mk (Cocycle.mk
      (Cochain.single (p := -(n : ℤ)) (q := 0) ((chainsXIso R E n).hom ≫ s ≫ resι R F) n)
      ((n + 1 : ℕ) : ℤ) (by push_cast; ring) ?_), _, rfl, rfl⟩
    rw [differential, hs, zero_comp, comp_zero, Cochain.single_zero, smul_zero]
  · obtain ⟨z, rfl, hz⟩ := hx
    obtain ⟨z', rfl, hz'⟩ := hx'
    refine ⟨z + z', (CohomologyClass.mk_add z z').symm, ?_⟩
    change z.1 + z'.1 = _
    rw [hz, hz', ← ClsBasic.single_add', Preadditive.add_comp, Preadditive.comp_add]
  · obtain ⟨z, rfl, hz⟩ := hx
    obtain ⟨z', rfl, hz'⟩ := hx'
    have : z = z' := Cocycle.ext (hz.trans hz'.symm)
    rw [this]
  · obtain ⟨z, rfl, hz⟩ := hx
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n : ℤ) (by push_cast; ring)]
    refine ⟨(((n + 1 : ℕ) : ℤ)).negOnePow •
      Cochain.single (p := -(n : ℤ)) (q := 0) ((chainsXIso R E n).hom ≫ t ≫ resι R F) n, ?_⟩
    rw [δ_units_smul, differential, smul_smul, Int.units_mul_self, one_smul, hz]
  · obtain ⟨z, rfl, hz⟩ := hx
    refine ⟨zcomp (Cocycle.ofHom ((chains R).map f)) z (zero_add _), rfl, ?_⟩
    change (Cochain.ofHom ((chains R).map f)).comp z.1 (zero_add _) = _
    rw [hz, ClsBasic.ofHom_comp_single, ← Category.assoc, ClsBasic.chainsXIso_nat]
    simp only [Category.assoc]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsSepGlueOfSurjectiveFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsSepGlueOfSurjectiveFamily
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem sec_sep_glue_of_points : ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}) (ι : Type) (V : ι → Scheme.{0}) (j : ∀ i, V i ⟶ U), (∀ i, Etale (j i)) → (∀ u : U, ∃ i v, j i v = u) → (∀ x : Sec F U, (∀ i, Sec.res (j i) x = 0) → x = 0) ∧ ∀ y : ∀ i, Sec F (V i), (∀ i k, Sec.res (pullback.fst (j i) (j k)) (y i) = Sec.res (pullback.snd (j i) (j k)) (y k)) → ∃ x : Sec F U, ∀ i, Sec.res (j i) x = y i := by
  intro R _ F U ι V j hE hS
  have hcov : Sieve.generate (Presieve.ofArrows V j) ∈ Scheme.etaleTopology U := by
    apply Precoverage.generate_mem_toGrothendieck
    refine (Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).2 ⟨fun u => ?_, hE⟩
    obtain ⟨i, v, hv⟩ := hS u
    exact ⟨i, v, hv⟩
  have hF : Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) := by
    rw [← isSheaf_iff_isSheaf_of_type]
    exact (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget _)).1 F.property
  have hfor := (Presieve.isSheafFor_iff_generate _).2 (hF _ hcov)
  rw [Presieve.isSheafFor_arrows_iff_pullbacks] at hfor
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · obtain ⟨t, -, ht⟩ := hfor (fun _ => 0) (fun i k => by
      change (F.obj.map (pullback.fst (j i) (j k)).op).hom 0 = (F.obj.map (pullback.snd (j i) (j k)).op).hom 0
      rw [map_zero, map_zero])
    have h0 : (0 : Sec F U) = t := ht 0 (fun i => by
      change (F.obj.map (j i).op).hom 0 = 0
      exact map_zero _)
    exact (ht x hx).trans h0.symm
  · obtain ⟨t, ht, -⟩ := hfor y hy
    exact ⟨t, ht⟩

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsSepGlueOfSurjectiveFamilyStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSheafSections_sep_glue_of_surjective_family : ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}) (ι : Type) (V : ι → Scheme.{0}) (j : ∀ i, V i ⟶ U), (∀ i, Etale (j i)) → (∀ u : U, ∃ i v, j i v = u) → (∀ x : Sec F U, (∀ i, Sec.res (j i) x = 0) → x = 0) ∧ ∀ y : ∀ i, Sec F (V i), (∀ i k, Sec.res (pullback.fst (j i) (j k)) (y i) = Sec.res (pullback.snd (j i) (j k)) (y k)) → ∃ x : Sec F U, ∀ i, Sec.res (j i) x = y i := by
  first | exact @GlobalTheory.EtC.sec_sep_glue_of_points | exact GlobalTheory.EtC.sec_sep_glue_of_points | (intros; apply GlobalTheory.EtC.sec_sep_glue_of_points <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendScalarsUliftHomAdditive
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC

section ExtScalars
variable {R S : Type} [CommRing R] [CommRing S]

def uliftHom (φ : R →+* S) : ULift.{1} R →+* ULift.{1} S :=
  (ULift.ringEquiv.symm : S ≃+* ULift.{1} S).toRingHom.comp (φ.comp (ULift.ringEquiv : ULift.{1} R ≃+* R).toRingHom)

instance extendScalars_uliftHom_additive (φ : R →+* S) :
    (ModuleCat.extendScalars.{1, 1, 1} (uliftHom φ)).Additive where
  map_add {M N} g h := by
    letI := (uliftHom φ).toAlgebra
    ext m
    exact TensorProduct.tmul_add (R := ULift.{1} R) (1 : ULift.{1} S) (g.hom m) (h.hom m)

def extSh (φ : R →+* S) : Shv R ⥤ Shv S :=
  sheafToPresheaf _ _ ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.extendScalars.{1, 1, 1} (uliftHom φ)) ⋙
    presheafToSheaf _ _

instance (φ : R →+* S) : (extSh φ).Additive := by
  unfold extSh; infer_instance

def extSh.sec (φ : R →+* S) (F : Shv R) (U : Scheme.{0}) : Sec F U →+ Sec ((extSh φ).obj F) U :=
  ((toSheafify Scheme.etaleTopology (F.obj ⋙ ModuleCat.extendScalars.{1, 1, 1} (uliftHom φ))).app (op U)).hom.toAddMonoidHom.comp
    ((ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom φ)).unit.app (F.obj.obj (op U))).hom.toAddMonoidHom

theorem extSh.sec_res (φ : R →+* S) (F : Shv R) {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec F U) :
    Sec.res g (extSh.sec φ F U a) = extSh.sec φ F V (Sec.res g a) := by
  have e1 := (toSheafify Scheme.etaleTopology (F.obj ⋙ ModuleCat.extendScalars.{1, 1, 1} (uliftHom φ))).naturality g.op
  have e2 := (ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom φ)).unit.naturality (F.obj.map g.op)
  have h1 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom e1)
    (((ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom φ)).unit.app (F.obj.obj (op U))).hom a)
  have h2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom e2) a
  exact h1.symm.trans (congrArg _ h2.symm)

theorem extSh.sec_map (φ : R →+* S) {F G : Shv R} (f : F ⟶ G) (U : Scheme.{0}) (a : Sec F U) :
    Sec.map ((extSh φ).map f) (extSh.sec φ F U a) = extSh.sec φ G U (Sec.map f a) := by
  have e1 := NatTrans.congr_app (toSheafify_naturality Scheme.etaleTopology
      (Functor.whiskerRight f.hom (ModuleCat.extendScalars.{1, 1, 1} (uliftHom φ)))) (op U)
  have e2 := (ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom φ)).unit.naturality (f.hom.app (op U))
  have h1 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom e1)
    (((ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (uliftHom φ)).unit.app (F.obj.obj (op U))).hom a)
  have h2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom e2) a
  exact h1.symm.trans (congrArg _ h2.symm)

abbrev extCx (φ : R →+* S) (I : Cx R) : Cx S := ((extSh φ).mapHomologicalComplex _).obj I

def extπ (φ : R →+* S) (I : Cx R) : SemiMap I (extCx φ I) where
  app U s := extSh.sec φ (I.X s) U
  nat g s a := extSh.sec_res φ (I.X s) g a
  comm U s t a := extSh.sec_map φ (I.d s t) U a

def extAug (φ : R →+* S) (F : Shv R) : sgl ((extSh φ).obj F) ⟶ extCx φ (res R F) :=
  (HomologicalComplex.singleMapHomologicalComplex (extSh φ) (ComplexShape.up ℤ) 0).inv.app F ≫
    ((extSh φ).mapHomologicalComplex _).map (resAug F)

end ExtScalars

end GlobalTheory.EtC

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackBiprodInlInrBijective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackBiprodInlInrBijective
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.BiprodCls

variable {R : Type} [CommRing R]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.BiprodCls.cpull_cpull {K L M : _root_.GlobalTheory.EtC.Cx R} (f : K ⟶ L)
    (g : L ⟶ M) (I : _root_.GlobalTheory.EtC.Cx R) (n : ℤ) (x : CohomologyClass M I n) :
    _root_.GlobalTheory.EtC.cpull f I n (_root_.GlobalTheory.EtC.cpull g I n x) =
      _root_.GlobalTheory.EtC.cpull (f ≫ g) I n x := by
  obtain ⟨b, rfl⟩ := CohomologyClass.mk_surjective x
  unfold _root_.GlobalTheory.EtC.cpull
  simp only [_root_.GlobalTheory.EtC.cpre_mk]
  congr 1
  apply Cocycle.ext
  simp [_root_.GlobalTheory.EtC.zcomp, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.BiprodCls.cpull_add {K L : _root_.GlobalTheory.EtC.Cx R} (f g : K ⟶ L)
    (I : _root_.GlobalTheory.EtC.Cx R) (n : ℤ) (x : CohomologyClass L I n) :
    _root_.GlobalTheory.EtC.cpull (f + g) I n x =
      _root_.GlobalTheory.EtC.cpull f I n x + _root_.GlobalTheory.EtC.cpull g I n x := by
  obtain ⟨b, rfl⟩ := CohomologyClass.mk_surjective x
  unfold _root_.GlobalTheory.EtC.cpull
  simp only [_root_.GlobalTheory.EtC.cpre_mk, ← CohomologyClass.mk_add]
  congr 1
  apply Cocycle.ext
  simp [_root_.GlobalTheory.EtC.zcomp, Cochain.add_comp]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.BiprodCls.cpull_zero {K L : _root_.GlobalTheory.EtC.Cx R}
    (I : _root_.GlobalTheory.EtC.Cx R) (n : ℤ) (x : CohomologyClass L I n) :
    _root_.GlobalTheory.EtC.cpull (0 : K ⟶ L) I n x = 0 := by
  obtain ⟨b, rfl⟩ := CohomologyClass.mk_surjective x
  unfold _root_.GlobalTheory.EtC.cpull
  simp only [_root_.GlobalTheory.EtC.cpre_mk, ← CohomologyClass.mk_zero]
  congr 1
  apply Cocycle.ext
  simp [_root_.GlobalTheory.EtC.zcomp]

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable {R : Type} [CommRing R] in
theorem _root_.GlobalTheory.EtC.BiprodCls.cpull_id {K : _root_.GlobalTheory.EtC.Cx R}
    (I : _root_.GlobalTheory.EtC.Cx R) (n : ℤ) (x : CohomologyClass K I n) :
    _root_.GlobalTheory.EtC.cpull (𝟙 K) I n x = x := by
  obtain ⟨b, rfl⟩ := CohomologyClass.mk_surjective x
  unfold _root_.GlobalTheory.EtC.cpull
  simp only [_root_.GlobalTheory.EtC.cpre_mk]
  congr 1
  apply Cocycle.ext
  simp [_root_.GlobalTheory.EtC.zcomp]

end GlobalTheory.EtC.BiprodCls

namespace GlobalTheory.EtC
open BiprodCls

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
theorem _root_.GlobalTheory.EtC.cpull_biprod_bijective : ∀ (R : Type) [CommRing R]
    (K L I : _root_.GlobalTheory.EtC.Cx R) (n : ℤ),
    Function.Bijective fun x : CohomologyClass (K ⊞ L) I n =>
      (_root_.GlobalTheory.EtC.cpull (biprod.inl : K ⟶ K ⊞ L) I n x,
        _root_.GlobalTheory.EtC.cpull (biprod.inr : L ⟶ K ⊞ L) I n x) := by
  intro R _ K L I n
  rw [Function.bijective_iff_has_inverse]
  refine ⟨fun y => _root_.GlobalTheory.EtC.cpull (biprod.fst : K ⊞ L ⟶ K) I n y.1 +
    _root_.GlobalTheory.EtC.cpull (biprod.snd : K ⊞ L ⟶ L) I n y.2, fun x => ?_, fun y => ?_⟩
  · simp only [_root_.GlobalTheory.EtC.BiprodCls.cpull_cpull, ← _root_.GlobalTheory.EtC.BiprodCls.cpull_add,
      biprod.total, _root_.GlobalTheory.EtC.BiprodCls.cpull_id]
  · obtain ⟨a, b⟩ := y
    simp only [map_add (f := _), _root_.GlobalTheory.EtC.BiprodCls.cpull_cpull, biprod.inl_fst, biprod.inl_snd,
      biprod.inr_fst, biprod.inr_snd, _root_.GlobalTheory.EtC.BiprodCls.cpull_id,
      _root_.GlobalTheory.EtC.BiprodCls.cpull_zero, add_zero, zero_add]

end GlobalTheory.EtC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackBiprodInlInrBijectiveStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
theorem _root_.GlobalTheory.T.hypercohomologyPullback_biprod_inl_inr_bijective : ∀ (R : Type) [CommRing R] (K L I : Cx R) (n : ℤ), Function.Bijective fun x : CohomologyClass (K ⊞ L) I n => (cpull (biprod.inl : K ⟶ K ⊞ L) I n x, cpull (biprod.inr : L ⟶ K ⊞ L) I n x) := by
  first | exact @GlobalTheory.EtC.cpull_biprod_bijective | exact GlobalTheory.EtC.cpull_biprod_bijective | (intros; apply GlobalTheory.EtC.cpull_biprod_bijective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyMappingConeSecondVariableExact
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyMappingConeSecondVariableExact
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.ConeTgt

variable {R : Type} [CommRing R]

theorem cls_eq' {K I : Cx R} {n : ℤ} (x y : Cocycle K I n) (m : ℤ) (hm : m + 1 = n) (β : Cochain K I m)
    (h : (x : Cochain K I n) = (y : Cochain K I n) + δ m n β) :
    CohomologyClass.mk x = CohomologyClass.mk y := by
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ m hm]
  exact ⟨β, by simp [h]⟩

end GlobalTheory.EtC.ConeTgt

private theorem coe_zcomp {R : Type} [CommRing R] {K L M : Cx R} {m n k : ℤ}
    (a : Cocycle K L m) (b : Cocycle L M n) (h : m + n = k) :
    ((zcomp a b h : Cocycle K M k) : Cochain K M k) = a.1.comp b.1 h := rfl

private theorem cohomologyClass_mk_eq_zero_of_eq_δ {R : Type} [CommRing R] {K L : Cx R} {n : ℤ} (x : Cocycle K L n)
    (m : ℤ) (hm : m + 1 = n) (β : Cochain K L m) (h : (x : Cochain K L n) = δ m n β) :
    CohomologyClass.mk x = 0 := by
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ m hm]
  exact ⟨β, h.symm⟩

theorem GlobalTheory.EtC.coneSeqTgt_exact : ∀ (R : Type) [CommRing R] (K : Cx R) {I J : Cx R} (f : I ⟶ J) (n : ℤ), Function.Exact (cpush K f n) (cpush K (mappingCone.inr f) n) ∧ Function.Exact (cpush K (mappingCone.inr f) n) (cpost K (mappingCone.fst f) n (n + 1) rfl) ∧ Function.Exact (cpost K (mappingCone.fst f) n (n + 1) rfl) (cpush K f (n + 1)) := by
  intro R _ K I J f n
  refine ⟨fun c => ?_, fun c => ?_, fun c => ?_⟩
  · obtain ⟨y, rfl⟩ := c.mk_surjective
    constructor
    · intro hy
      simp only [cpush, cpost_mk] at hy
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at hy
      obtain ⟨γ, hγ⟩ := hy
      rw [coe_zcomp] at hγ
      have ha : δ n (n + 1) (γ.comp (mappingCone.fst f).1 (by omega : n - 1 + 1 = n)) = 0 := by
        rw [δ_comp γ (mappingCone.fst f).1 _ n 2 (n + 1) rfl (by omega) rfl,
          Cocycle.δ_eq_zero, hγ]
        simp [Cochain.comp_assoc_of_second_is_zero_cochain, mappingCone.inr_fst]
      refine ⟨CohomologyClass.mk (Cocycle.mk _ (n + 1) rfl ha), ?_⟩
      simp only [cpush, cpost_mk]
      refine GlobalTheory.EtC.ConeTgt.cls_eq' _ _ (n - 1) (by omega)
        (-(γ.comp (mappingCone.snd f) (add_zero _))) ?_
      rw [coe_zcomp, δ_neg, δ_comp_zero_cochain _ _ _ (by omega), mappingCone.δ_snd, hγ]
      simp [Cochain.comp_assoc_of_second_is_zero_cochain,
        Cochain.comp_assoc_of_third_is_zero_cochain, mappingCone.inr_snd]
    · rintro ⟨c', hc'⟩
      rw [← hc']
      obtain ⟨x, rfl⟩ := c'.mk_surjective
      simp only [cpush, cpost_mk]
      refine cohomologyClass_mk_eq_zero_of_eq_δ _ (n + -1) (by omega) (x.1.comp (mappingCone.inl f) rfl) ?_
      rw [δ_comp x.1 (mappingCone.inl f) rfl (n + 1) 0 n (by omega) rfl (neg_add_cancel 1),
        mappingCone.δ_inl, Cocycle.δ_eq_zero]
      simp [coe_zcomp, Cochain.comp_assoc_of_second_is_zero_cochain, Cochain.ofHom_comp]
  · obtain ⟨z, rfl⟩ := c.mk_surjective
    constructor
    · intro hz
      rw [cpost_mk, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n rfl] at hz
      obtain ⟨c₀, hc₀⟩ := hz
      rw [coe_zcomp] at hc₀
      have hy : δ n (n + 1) (z.1.comp (mappingCone.snd f) (add_zero n) +
          c₀.comp (Cochain.ofHom f) (add_zero n)) = 0 := by
        rw [δ_add, δ_comp_zero_cochain _ _ _ rfl, mappingCone.δ_snd, δ_comp_ofHom, hc₀,
          Cocycle.δ_eq_zero]
        simp [Cochain.comp_assoc_of_third_is_zero_cochain]
      refine ⟨CohomologyClass.mk (Cocycle.mk _ (n + 1) rfl hy), ?_⟩
      simp only [cpush, cpost_mk]
      refine GlobalTheory.EtC.ConeTgt.cls_eq' _ _ (n + -1) (by omega)
        (c₀.comp (mappingCone.inl f) rfl) ?_
      rw [coe_zcomp, δ_comp c₀ (mappingCone.inl f) rfl (n + 1) 0 n (by omega) rfl
        (neg_add_cancel 1), mappingCone.δ_inl, hc₀]
      rw [mappingCone.ext_cochain_to_iff _ n (n + 1) rfl]
      constructor
      · simp [Cochain.comp_assoc_of_second_is_zero_cochain, Cochain.add_comp]
      · simp [Cochain.comp_assoc_of_second_is_zero_cochain,
          Cochain.comp_assoc_of_third_is_zero_cochain, Cochain.add_comp]
    · rintro ⟨c', hc'⟩
      rw [← hc']
      obtain ⟨y, rfl⟩ := c'.mk_surjective
      simp only [cpush, cpost_mk]
      refine cohomologyClass_mk_eq_zero_of_eq_δ _ n rfl 0 ?_
      simp [coe_zcomp, Cochain.comp_assoc_of_second_is_zero_cochain, mappingCone.inr_fst]
  · obtain ⟨w, rfl⟩ := c.mk_surjective
    constructor
    · intro hw
      simp only [cpush, cpost_mk] at hw
      rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ n rfl] at hw
      obtain ⟨b, hb⟩ := hw
      rw [coe_zcomp] at hb
      refine ⟨CohomologyClass.mk (mappingCone.liftCocycle f w (-b) rfl
        (by rw [δ_neg, hb]; simp)), ?_⟩
      rw [cpost_mk]
      congr 1
      apply Cocycle.ext
      rw [coe_zcomp]
      simp [mappingCone.liftCochain_fst]
    · rintro ⟨c', hc'⟩
      rw [← hc']
      obtain ⟨z, rfl⟩ := c'.mk_surjective
      simp only [cpush, cpost_mk]
      refine cohomologyClass_mk_eq_zero_of_eq_δ _ n rfl (-(z.1.comp (mappingCone.snd f) (add_zero n))) ?_
      rw [δ_neg, δ_comp_zero_cochain _ _ _ rfl, mappingCone.δ_snd, Cocycle.δ_eq_zero]
      simp [coe_zcomp, Cochain.comp_assoc_of_third_is_zero_cochain]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyMappingConeSecondVariableExactStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hypercohomology_mappingCone_second_variable_exact : ∀ (R : Type) [CommRing R] (K : Cx R) {I J : Cx R} (f : I ⟶ J) (n : ℤ), Function.Exact (cpush K f n) (cpush K (mappingCone.inr f) n) ∧ Function.Exact (cpush K (mappingCone.inr f) n) (cpost K (mappingCone.fst f) n (n + 1) rfl) ∧ Function.Exact (cpost K (mappingCone.fst f) n (n + 1) rfl) (cpush K f (n + 1)) := by
  first | (exact @GlobalTheory.EtC.coneSeqTgt_exact) | (exact GlobalTheory.EtC.coneSeqTgt_exact) | (intros; apply GlobalTheory.EtC.coneSeqTgt_exact  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafComplexMappingConeAcyclicOfQuasiIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafComplexMappingConeAcyclicOfQuasiIso
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory

theorem mappingCone_acyclic_of_quasiIso {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]
    {K L : CochainComplex 𝒜 ℤ} (u : K ⟶ L) [QuasiIso u] :
    (CochainComplex.mappingCone u).Acyclic := by
  rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
  have hu : HomotopyCategory.quasiIso 𝒜 (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).map u) := by
    rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
    exact (inferInstance : QuasiIso u)
  rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic] at hu
  exact ((HomotopyCategory.subcategoryAcyclic 𝒜).trW_iff_of_distinguished _
    (HomotopyCategory.mappingCone_triangleh_distinguished u)).1 hu

theorem EtC.mappingCone_acyclic :
    ∀ (R : Type) [CommRing R] {C J : Cx R} (u : C ⟶ J) [QuasiIso u], (mappingCone u).Acyclic :=
  fun _ _ _ _ u _ => mappingCone_acyclic_of_quasiIso u

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafComplexMappingConeAcyclicOfQuasiIsoStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSheafComplex_mappingCone_acyclic_of_quasiIso : ∀ (R : Type) [CommRing R] {C J : Cx R} (u : C ⟶ J) [QuasiIso u], (mappingCone u).Acyclic := by
  first | exact @GlobalTheory.EtC.mappingCone_acyclic | exact GlobalTheory.EtC.mappingCone_acyclic | (intros; apply GlobalTheory.EtC.mappingCone_acyclic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIndEtaleAlgebraOfStrictlyHenselianEtaleStalkAf
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIndEtaleAlgebraOfStrictlyHenselianEtaleStalkAf
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC

theorem isIndEtale_comp_etale {A B O : Type} [CommRing A] [CommRing B] [CommRing O] (φ : A →+* B)
    (hφ : φ.Etale) (g : B →+* O) (hg : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale g) :
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (g.comp φ) := by
  obtain ⟨J, _, _, D, s, t, hs, hj⟩ := hg
  refine ⟨J, inferInstance, inferInstance, D, (Functor.const J).map (CommRingCat.ofHom φ) ≫ s, t, hs,
    fun j => ⟨?_, ?_⟩⟩
  · show RingHom.Etale ((s.app j).hom.comp φ)
    exact RingHom.Etale.stableUnderComposition _ _ hφ (hj j).1
  · have h2 := (hj j).2
    show CommRingCat.ofHom φ ≫ s.app j ≫ t.app j = CommRingCat.ofHom (g.comp φ)
    rw [h2]
    rfl

theorem isStalk_affine : ∀ (A : Type) [CommRing A] (O : Type) [CommRing O]
    (s : Spec (CommRingCat.of O) ⟶ Spec (CommRingCat.of A)), IsStalk O s →
    ∃ _ : Algebra A O, SH O ∧ IndEt A O ∧ s = Spec.map (CommRingCat.ofHom (algebraMap A O)) := by
  intro A _ O _ s hs
  obtain ⟨hSH, A', _, _, j, hj, hind, rfl⟩ := hs
  set φ := Spec.preimage j with hφdef
  have hjφ : Spec.map φ = j := Spec.map_preimage j
  have hφ : φ.hom.Etale := by
    rw [← hjφ] at hj
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp hj
  letI : Algebra A O := ((algebraMap A' O).comp φ.hom).toAlgebra
  refine ⟨this, hSH, ?_, ?_⟩
  · exact isIndEtale_comp_etale φ.hom hφ (algebraMap A' O) hind
  · rw [← hjφ, ← Spec.map_comp]
    rfl

end GlobalTheory.EtC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIndEtaleAlgebraOfStrictlyHenselianEtaleStalkAfStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIndEtaleAlgebra_of_strictlyHenselianEtaleStalk_affine : ∀ (A : Type) [CommRing A] (O : Type) [CommRing O] (s : Spec (CommRingCat.of O) ⟶ Spec (CommRingCat.of A)), IsStalk O s → ∃ _ : Algebra A O, SH O ∧ IndEt A O ∧ s = Spec.map (CommRingCat.ofHom (algebraMap A O)) := by
  first | (exact @GlobalTheory.EtC.isStalk_affine) | (exact GlobalTheory.EtC.isStalk_affine) | (intros; apply GlobalTheory.EtC.isStalk_affine  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfEtaleCohomologyEquivalenceDiagram
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfEtaleCohomologyEquivalenceDiagram
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem ContCone.iff_of_eqv (R : Type) [CommRing R] (F : Shv R) (I : Type) [SmallCategory I] [IsCofiltered I]
    (G G' : I ⥤ Spc) (c : Cone G) (c' : Cone G') (α : G ⟶ G') (β : c.pt ⟶ c'.pt)
    (h : ∀ i, c.π.app i ≫ α.app i = β ≫ c'.π.app i) (hα : ∀ i, Eqv R (α.app i) F) (hβ : Eqv R β F) :
    ContCone R F c ↔ ContCone R F c' := by
  have hsq : ∀ n i (y' : H R (G'.obj i) F n),
      pull R (c.π.app i) F n (pull R (α.app i) F n y') = pull R β F n (pull R (c'.π.app i) F n y') := by
    intro n i y'
    rw [← pull_comp, ← pull_comp, h i]
  have hnat : ∀ n {k i : I} (f : k ⟶ i) (y' : H R (G'.obj i) F n),
      pull R (G.map f) F n (pull R (α.app i) F n y') = pull R (α.app k) F n (pull R (G'.map f) F n y') := by
    intro n k i f y'
    rw [← pull_comp, ← pull_comp, α.naturality f]
  constructor
  · intro hc n
    refine ⟨fun x' => ?_, fun i y' hy' => ?_⟩
    · obtain ⟨i, y, hy⟩ := (hc n).1 (pull R β F n x')
      obtain ⟨y', rfl⟩ := (hα i n).2 y
      refine ⟨i, y', (hβ n).1 ?_⟩
      rw [← hsq, hy]
    · obtain ⟨k, f, hf⟩ := (hc n).2 i (pull R (α.app i) F n y') (by rw [hsq, hy', map_zero])
      refine ⟨k, f, (hα k n).1 ?_⟩
      rw [← hnat, hf, map_zero]
  · intro hc n
    refine ⟨fun x => ?_, fun i y hy => ?_⟩
    · obtain ⟨x', rfl⟩ := (hβ n).2 x
      obtain ⟨i, y', hy'⟩ := (hc n).1 x'
      exact ⟨i, pull R (α.app i) F n y', by rw [hsq, hy']⟩
    · obtain ⟨y', rfl⟩ := (hα i n).2 y
      have h0 : pull R (c'.π.app i) F n y' = 0 := (hβ n).1 (by rw [← hsq, hy, map_zero])
      obtain ⟨k, f, hf⟩ := (hc n).2 i y' h0
      exact ⟨k, f, by rw [hnat, hf, map_zero]⟩

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfEtaleCohomologyEquivalenceDiagramStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.of_etaleCohomologyEquivalence_diagram : ∀ (R : Type) [CommRing R] (F : Shv R) (I : Type) [SmallCategory I] [IsCofiltered I] (G G' : I ⥤ Spc) (c : Cone G) (c' : Cone G') (α : G ⟶ G') (β : c.pt ⟶ c'.pt), (∀ i, c.π.app i ≫ α.app i = β ≫ c'.π.app i) → (∀ i, Eqv R (α.app i) F) → Eqv R β F → (ContCone R F c ↔ ContCone R F c') := by
  first | (exact @GlobalTheory.EtC.ContCone.iff_of_eqv) | (exact GlobalTheory.EtC.ContCone.iff_of_eqv) | (intros; apply GlobalTheory.EtC.ContCone.iff_of_eqv  <;> assumption)
end
end
