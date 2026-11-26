module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
public import Development.EtaleCohomology.EtaleTrace.PtCoverPf
public import Development.EtaleCohomology.TateTwists.TPaTensUnivPf

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleTrace.EtaleTateTwistSectionConstantOnPointsOfConnected
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleTrace

def PtCov : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} (p : X ⟶ S k), IsProper p →
  ∀ Sv : Sieve X, Sv ∈ Scheme.etaleTopology X → ∃ T : Sieve X, T ∈ Scheme.etaleTopology X ∧
    ∀ (V : Scheme.{0}) (g : V ⟶ X), T.arrows g → ∃ (U : Scheme.{0}) (g' : U ⟶ X) (h : V ⟶ U),
      Sv.arrows g' ∧ h ≫ g' = g ∧ ∃ w : S k ⟶ U, w ≫ g' ≫ p = 𝟙 _

def EtaleTateTwistSectionConstantOnPointsOfConnectedProper : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 → ∀ j : ℕ,
  ∀ {X : Scheme.{0}} (p : X ⟶ S k), IsProper p → ∀ s : Sec (tw (l ^ j) 0) X,
    (ConnectedSpace X → ∀ y y' : Pt p, Sec.res y.1 s = Sec.res y'.1 s)

theorem q_nsmul {q : ℕ} {U : Scheme.{0}} (x : Sec (tw q 0) U) : q • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  have : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := ULift.ext (by simp)
  rw [this, zero_smul]

theorem res_comp {q : ℕ} {W V U : Scheme.{0}} (a : W ⟶ V) (b : V ⟶ U) (x : Sec (tw q 0) U) :
    Sec.res (a ≫ b) x = Sec.res a (Sec.res b x) := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem res_nsmul {q : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (c : ℕ) (x : Sec (tw q 0) U) :
    Sec.res g (c • x) = c • Sec.res g x := map_nsmul _ _ _

theorem res_zero' {q : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) : Sec.res g (0 : Sec (tw q 0) U) = 0 := map_zero _

theorem primK (k : Type) [Field k] [IsAlgClosed k] (q : ℕ) (hq : (q : k) ≠ 0) : Nonempty (Prim q k) := by
  have hq0 : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; simp at hq)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic q k)
    (ne_of_gt (Polynomial.degree_cyclotomic_pos q k hq0))
  refine ⟨⟨z, isUnit_iff_ne_zero.2 hq, ?_⟩⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact hz

theorem etale_tate_twist_zero_section_eq_zero_of_vanishing_at_points (hT : LateralTheory.EtaleFoundations.CongruenceLocalDecomposition.TwLoc) (hC : PtCov) (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k]
    (hl : (l : k) ≠ 0) (j : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) (hp : IsProper p) (s : Sec (tw (l ^ j) 0) X)
    (h : ∀ y : Pt p, Sec.res y.1 s = 0) : s = 0 := by
  haveI : NeZero (l ^ j) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hq : ((l ^ j : ℕ) : k) ≠ 0 := by push_cast; exact pow_ne_zero _ hl
  obtain ⟨ζ0⟩ := primK k (l ^ j) hq
  let φ : k →+* Γ(X, ⊤) := (p.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  obtain ⟨Sv, hSv, hSs⟩ := (hT (l ^ j) 0).1 X (ζ0.map φ) s
  obtain ⟨T, hTm, hTs⟩ := hC k p hp Sv hSv
  refine (EtaleFoundations.etale_sheaf_sections_glue_of_forget_isSheaf (ZMod (l ^ j)) (tw (l ^ j) 0) X).1 s 0 ⟨T, hTm, fun V g hg => ?_⟩
  obtain ⟨U, g', hh, hg', rfl, w, hw⟩ := hTs V g hg
  obtain ⟨c, hc⟩ := hSs U g' hg'
  have h0 : Sec.res g' s = 0 := by
    have e1 : Sec.res w (Sec.res g' s) = 0 := by
      rw [← res_comp]
      exact h ⟨w ≫ g', by rw [Category.assoc]; exact hw⟩
    rw [hc] at e1 ⊢
    rw [res_nsmul, (hT (l ^ j) 0).2.2] at e1
    obtain ⟨m, rfl⟩ := (hT (l ^ j) 0).2.1 (S k) _ c e1
    rw [mul_comm]
    first
      | (rw [mul_nsmul, q_nsmul, nsmul_zero])
      | (rw [mul_nsmul', q_nsmul, nsmul_zero])
      | (rw [mul_nsmul', q_nsmul, smul_zero])
      | (rw [mul_nsmul, q_nsmul, smul_zero])
  rw [res_comp, h0, res_zero', res_zero']

theorem tateTwistSections_determinedByPoints_of_constant (hT : LateralTheory.EtaleFoundations.CongruenceLocalDecomposition.TwLoc) (hC : PtCov) (hK : EtaleTateTwistSectionConstantOnPointsOfConnectedProper) : EtaleTateTwistSectionsDeterminedByPointsOfProper := by
  intro l _ k _ _ hl j X p hp s
  exact ⟨etale_tate_twist_zero_section_eq_zero_of_vanishing_at_points hT hC l k hl j p hp s, hK l k hl j p hp s⟩

end LateralTheory.EtaleTrace
end
end

section -- merged from Development.EtaleCohomology.EtaleTrace.PrimSplitPf
noncomputable section
open Polynomial

namespace LateralTheory.EtaleTrace

theorem ps_isUnit_of_quot {A : Type} [CommRing A] (x : A)
    (h : ∀ m : Ideal A, m.IsMaximal → Ideal.Quotient.mk m x ≠ 0) : IsUnit x := by
  by_contra hx
  obtain ⟨m, hm, hxm⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hx)
  exact h m hm (Ideal.Quotient.eq_zero_iff_mem.2 hxm)

theorem ps_aeval_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (x : A) (p : ℤ[X]) :
    aeval (f x) p = f (aeval x p) := by
  have := Polynomial.aeval_algHom_apply f.toIntAlgHom x p
  simpa using this

theorem ps_prim_field {q : ℕ} {K : Type} [Field K] [NeZero (q : K)] {x : K}
    (h2 : aeval x (cyclotomic q ℤ) = 0) : IsPrimitiveRoot x q := by
  refine (Polynomial.isRoot_cyclotomic_iff).1 ?_
  rw [Polynomial.IsRoot.def, ← Polynomial.map_cyclotomic_int, Polynomial.eval_map, ← algebraMap_int_eq, ← Polynomial.aeval_def]
  exact h2

theorem ps_prim_quot {q : ℕ} [NeZero q] {A : Type} [CommRing A] {ζ : A} (hq : IsUnit (q : A))
    (hζ : aeval ζ (cyclotomic q ℤ) = 0) (m : Ideal A) [m.IsMaximal] :
    IsPrimitiveRoot (Ideal.Quotient.mk m ζ) q := by
  let _ : Field (A ⧸ m) := Ideal.Quotient.field m
  have : NeZero ((q : ℕ) : A ⧸ m) := ⟨by
    have := hq.map (Ideal.Quotient.mk m)
    simpa using this.ne_zero⟩
  have h2 := ps_aeval_map (Ideal.Quotient.mk m) ζ (cyclotomic q ℤ)
  rw [hζ, map_zero] at h2
  exact ps_prim_field h2

theorem ps_pow_q {q : ℕ} {A : Type} [CommRing A] {ζ : A} (hζ : aeval ζ (cyclotomic q ℤ) = 0) : ζ ^ q = 1 := by
  obtain ⟨g, hg⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
  have := congrArg (aeval ζ) hg
  simp only [map_sub, map_pow, aeval_X, map_one, map_mul, hζ, zero_mul] at this
  exact sub_eq_zero.1 this

theorem ps_sub_one_unit {q : ℕ} [NeZero q] {A : Type} [CommRing A] {ζ w : A} (hq : IsUnit (q : A))
    (hζ : aeval ζ (cyclotomic q ℤ) = 0) (hw : w * ζ = 1) {k : ℕ} (hk0 : 0 < k) (hkq : k < q) : IsUnit (w ^ k - 1) := by
  refine ps_isUnit_of_quot _ fun m hm => ?_
  have hp := ps_prim_quot hq hζ m
  intro h0
  rw [map_sub, map_pow, map_one, sub_eq_zero] at h0
  have h1 : (Ideal.Quotient.mk m ζ) ^ k = 1 := by
    have := congrArg (Ideal.Quotient.mk m) (congrArg (· ^ k) hw)
    simp only [mul_pow, one_pow, map_mul, map_pow, map_one] at this
    rw [h0, one_mul] at this; exact this
  have := Nat.le_of_dvd hk0 (hp.dvd_of_pow_eq_one k h1)
  omega

theorem ps_cyc_unit {q : ℕ} [NeZero q] {A : Type} [CommRing A] {ζ : A} (hq : IsUnit (q : A))
    (hζ : aeval ζ (cyclotomic q ℤ) = 0) {i : ℕ} (hi : ¬ Nat.Coprime i q) : IsUnit (aeval (ζ ^ i) (cyclotomic q ℤ)) := by
  refine ps_isUnit_of_quot _ fun m hm => ?_
  have hp := ps_prim_quot hq hζ m
  intro h0
  have h2 := ps_aeval_map (Ideal.Quotient.mk m) (ζ ^ i) (cyclotomic q ℤ)
  rw [h0, map_pow] at h2
  let _ : Field (A ⧸ m) := Ideal.Quotient.field m
  have : NeZero ((q : ℕ) : A ⧸ m) := ⟨by
    have := hq.map (Ideal.Quotient.mk m)
    simpa using this.ne_zero⟩
  have hp2 := ps_prim_field h2
  exact hi ((hp.pow_iff_coprime (Nat.pos_of_ne_zero (NeZero.ne q)) i).1 hp2)

theorem ps_pow_eq {A : Type} [CommRing A] {e x y : A} (h : e * x = e * y) (n : ℕ) : e * x ^ n = e * y ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, ← mul_assoc, ih, mul_assoc, mul_comm (y ^ n), ← mul_assoc, h]; ring

theorem ps_aeval_eq {A : Type} [CommRing A] {e x y : A} (h : e * x = e * y) (p : ℤ[X]) :
    e * aeval x p = e * aeval y p := by
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul_comm, mul_smul_comm, ps_pow_eq h]

theorem ps_split {q : ℕ} [NeZero q] {A : Type} [CommRing A] {ζ ξ : A} (hq : IsUnit (q : A))
    (hζ : aeval ζ (cyclotomic q ℤ) = 0) (hξ : aeval ξ (cyclotomic q ℤ) = 0) : ∃ e : Fin q → A,
    (∀ i, IsIdempotentElem (e i)) ∧ ∑ i, e i = 1 ∧ (∀ i, e i * ξ = e i * ζ ^ (i : ℕ)) ∧
    (∀ i : Fin q, ¬ Nat.Coprime (i : ℕ) q → e i = 0) := by
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  obtain ⟨u, hu⟩ := hq
  set c : A := ((u⁻¹ : Aˣ) : A) with hcdef
  have hc : c * q = 1 := by rw [← hu, hcdef, Units.inv_mul]
  have hζq := ps_pow_q hζ
  have hξq := ps_pow_q hξ
  set w : A := ζ ^ (q - 1) with hwdef
  have hw : w * ζ = 1 := by rw [hwdef, ← pow_succ, Nat.sub_add_cancel hq0, hζq]
  have hwq : w ^ q = 1 := by rw [hwdef, ← pow_mul, mul_comm, pow_mul, hζq, one_pow]
  let η : Fin q → A := fun i => ξ * w ^ (i : ℕ)
  let S : Fin q → A := fun i => ∑ k ∈ Finset.range q, (η i) ^ k
  have hη : ∀ i, (η i) ^ q = 1 := fun i => by
    simp only [η]; rw [mul_pow, hξq, ← pow_mul, mul_comm (i : ℕ) q, pow_mul, hwq, one_pow, one_mul]
  have hSη : ∀ i, S i * η i = S i := fun i => by
    have := geom_sum_mul (η i) q
    rw [hη, sub_self, mul_sub, mul_one, sub_eq_zero] at this
    exact this
  have hSpow : ∀ i k, S i * (η i) ^ k = S i := fun i k => by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← mul_assoc, ih, hSη]
  have hSS : ∀ i, S i * S i = q * S i := fun i => by
    conv_lhs => rw [show S i * S i = S i * ∑ k ∈ Finset.range q, (η i) ^ k from rfl]
    rw [Finset.mul_sum]
    simp only [hSpow, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  refine ⟨fun i => c * S i, fun i => ?_, ?_, fun i => ?_, fun i hi => ?_⟩
  · show c * S i * (c * S i) = c * S i
    calc c * S i * (c * S i) = c * (c * (S i * S i)) := by ring
      _ = c * ((c * q) * S i) := by rw [hSS]; ring
      _ = c * S i := by rw [hc, one_mul]
  · rw [← Finset.mul_sum]
    have hT : ∀ k ∈ Finset.range q, ∑ i : Fin q, ξ ^ k * (w ^ k) ^ (i : ℕ) = if k = 0 then (q : A) else 0 := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun i => (w ^ k) ^ i)]
      split_ifs with h0
      · subst h0; simp
      · have hu2 := ps_sub_one_unit (ζ := ζ) ⟨u, hu⟩ hζ hw (Nat.pos_of_ne_zero h0) hk
        have hg : (∑ i ∈ Finset.range q, (w ^ k) ^ i) * (w ^ k - 1) = 0 := by
          rw [geom_sum_mul, ← pow_mul, mul_comm k q, pow_mul, hwq, one_pow, sub_self]
        rw [(hu2.mul_left_eq_zero).1 hg, mul_zero]
    have hsum : ∑ i : Fin q, S i = (q : A) := by
      simp only [S, η]
      rw [Finset.sum_comm]
      have hT2 : ∀ k ∈ Finset.range q, ∑ x : Fin q, (ξ * w ^ (x : ℕ)) ^ k = if k = 0 then (q : A) else 0 :=
        fun k hk => by
          rw [← hT k hk]; exact Finset.sum_congr rfl fun i _ => by ring
      rw [Finset.sum_congr rfl hT2]
      rw [Finset.sum_ite_eq' (Finset.range q) 0, if_pos (Finset.mem_range.2 hq0)]
    rw [hsum, hc]
  · have h1 : c * S i * η i = c * S i := by rw [mul_assoc, hSη]
    calc c * S i * ξ = c * S i * ξ * (w * ζ) ^ (i : ℕ) := by rw [hw, one_pow, mul_one]
      _ = c * S i * η i * ζ ^ (i : ℕ) := by simp only [η]; rw [mul_pow]; ring
      _ = c * S i * ζ ^ (i : ℕ) := by rw [h1]
  · have h1 := ps_aeval_eq (e := c * S i) (x := ξ) (y := ζ ^ (i : ℕ)) ?_ (cyclotomic q ℤ)
    · rw [hξ, mul_zero] at h1
      exact ((ps_cyc_unit ⟨u, hu⟩ hζ hi).mul_left_eq_zero).1 h1.symm
    · have h1 : c * S i * η i = c * S i := by rw [mul_assoc, hSη]
      calc c * S i * ξ = c * S i * ξ * (w * ζ) ^ (i : ℕ) := by rw [hw, one_pow, mul_one]
        _ = c * S i * η i * ζ ^ (i : ℕ) := by simp only [η]; rw [mul_pow]; ring
        _ = c * S i * ζ ^ (i : ℕ) := by rw [h1]

theorem PrimSplit_of : PrimSplit := fun q _ A _ ζ ξ => ps_split ζ.2.1 ζ.2.2 ξ.2.2

end LateralTheory.EtaleTrace
end
end

section -- merged from Development.EtaleCohomology.EtaleTrace.CocEqPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CochainComplex.HomComplex Opposite

namespace LateralTheory.EtaleTrace

theorem free_ext (R : Type) [CommRing R] (P : PSh) {G : Shv R} (f g : (free R).obj P ⟶ G)
    (h : ∀ (U : Scheme.{0}) (x : P.obj (op U)),
      (f.hom.app (op U)).hom (freeGen R P U x) = (g.hom.app (op U)).hom (freeGen R P U x)) : f = g := by
  apply Sheaf.hom_ext
  refine sheafify_hom_ext (J := Scheme.etaleTopology) (P := (freeP R).obj P) f.hom g.hom G.property ?_
  ext U : 2
  apply ModuleCat.free_hom_ext
  rintro ⟨x⟩
  have := h U.unop x
  simp only [freeGen] at this
  simp only [freeP, ModuleCat.freeMk] at this
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply]
  exact this

theorem cocEq : CocEq := by
  intro R _ F X α β h
  apply Cocycle.ext
  apply Cochain.ext₀
  intro q
  rcases lt_trichotomy q 0 with hq | rfl | hq
  · have : (res R F).IsStrictlyGE 0 := by unfold res; infer_instance
    exact (CochainComplex.isZero_of_isStrictlyGE (res R F) 0 q hq).eq_of_tgt _ _
  · have key : (chainsXIso R (sch.obj X) 0).inv ≫ α.1.v _ _ (show -((0:ℕ):ℤ) + 0 = 0 by simp) =
        (chainsXIso R (sch.obj X) 0).inv ≫ β.1.v _ _ (show -((0:ℕ):ℤ) + 0 = 0 by simp) := by
      apply free_ext
      intro U x
      exact h U x
    have := congrArg (fun φ => (chainsXIso R (sch.obj X) 0).hom ≫ φ) key
    simpa using this
  · apply IsZero.eq_of_src
    apply HomologicalComplex.isZero_extend_X
    intro i hi
    change -(i:ℤ) = q at hi
    omega

theorem CocEq_of : CocEq := cocEq

end LateralTheory.EtaleTrace
end
end

section -- merged from Development.EtaleCohomology.EtaleTrace.TateTwistSectionConstantOnPointsOfTwLocPtCov
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleTrace

def ConnLoc : Prop := ∀ {X : Scheme.{0}}, ConnectedSpace X → ∀ (P Q : ∀ V : Scheme.{0}, (V ⟶ X) → Prop),
  (∀ (V W : Scheme.{0}) (g : V ⟶ X) (h : W ⟶ V), P V g → P W (h ≫ g)) →
  (∀ (V W : Scheme.{0}) (g : V ⟶ X) (h : W ⟶ V), Q V g → Q W (h ≫ g)) →
  (∀ (V : Scheme.{0}) (g : V ⟶ X), IsEmpty V → P V g ∧ Q V g) →
  (∀ (V : Scheme.{0}) (g : V ⟶ X), P V g → Q V g → IsEmpty V) →
  Loc X (fun V g => P V g ∨ Q V g) → Loc X P ∨ Loc X Q

def PtLift : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} (z : S k ⟶ X)
  (R : ∀ V : Scheme.{0}, (V ⟶ X) → Prop), Loc X R →
    ∃ (V : Scheme.{0}) (g : V ⟶ X) (w : S k ⟶ V), R V g ∧ w ≫ g = z

theorem ConnLoc_pf : ConnLoc := by
  intro X hX P Q hPs hQs hE hD hL
  obtain ⟨Sv, hSv, hSs⟩ := hL
  obtain ⟨𝒰, h𝒰⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hSv
  have hi : ∀ i, P (𝒰.X i) (𝒰.f i) ∨ Q (𝒰.X i) (𝒰.f i) := fun i => hSs _ _ (h𝒰 _ _ (Presieve.ofArrows.mk i))
  have hcov := ((Scheme.presieve₀_mem_precoverage_iff _).mp 𝒰.mem₀).1
  have hop : ∀ i, IsOpen (Set.range (𝒰.f i)) := fun i => by
    haveI : Etale (𝒰.f i) := 𝒰.map_prop i
    exact (𝒰.f i).isOpenMap.isOpen_range
  let A : Set X := ⋃ (i) (_ : P (𝒰.X i) (𝒰.f i)), Set.range (𝒰.f i)
  let B : Set X := ⋃ (i) (_ : ¬ P (𝒰.X i) (𝒰.f i)), Set.range (𝒰.f i)
  have hAo : IsOpen A := isOpen_iUnion fun i => isOpen_iUnion fun _ => hop i
  have hBo : IsOpen B := isOpen_iUnion fun i => isOpen_iUnion fun _ => hop i
  have hAB : ∀ x, x ∈ A ∨ x ∈ B := by
    intro x
    obtain ⟨i, hx⟩ := hcov x
    by_cases h : P (𝒰.X i) (𝒰.f i)
    · exact Or.inl (Set.mem_iUnion₂.2 ⟨i, h, hx⟩)
    · exact Or.inr (Set.mem_iUnion₂.2 ⟨i, h, hx⟩)
  have hdis : ∀ x, x ∈ A → x ∈ B → False := by
    intro x hA hB
    obtain ⟨i, hPi, a, ha⟩ := Set.mem_iUnion₂.1 hA
    obtain ⟨j, hPj, b, hb⟩ := Set.mem_iUnion₂.1 hB
    have hQj : Q (𝒰.X j) (𝒰.f j) := (hi j).resolve_left hPj
    obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := 𝒰.f i) (g := 𝒰.f j) a b (ha.trans hb.symm)
    have h1 := hPs _ _ _ (pullback.fst (𝒰.f i) (𝒰.f j)) hPi
    have h2 := hQs _ _ _ (pullback.snd (𝒰.f i) (𝒰.f j)) hQj
    rw [← pullback.condition] at h2
    exact (hD _ _ h1 h2).false z
  have hAc : IsClosed A := by
    have : A = Bᶜ := by
      ext x; constructor
      · intro hA hB; exact hdis x hA hB
      · intro hB; exact (hAB x).resolve_right hB
    rw [this]; exact hBo.isClosed_compl
  have hmem := Scheme.Cover.mem_grothendieckTopology 𝒰
  rcases isClopen_iff.1 ⟨hAc, hAo⟩ with h0 | h1
  · right
    refine ⟨_, hmem, fun V g hg => ?_⟩
    obtain ⟨W, h, g', ⟨i⟩, rfl⟩ := hg
    apply hQs
    by_cases hP : P (𝒰.X i) (𝒰.f i)
    · refine (hE _ _ ⟨fun a => ?_⟩).2
      have : 𝒰.f i a ∈ A := Set.mem_iUnion₂.2 ⟨i, hP, a, rfl⟩
      rw [h0] at this; exact this
    · exact (hi i).resolve_left hP
  · left
    refine ⟨_, hmem, fun V g hg => ?_⟩
    obtain ⟨W, h, g', ⟨i⟩, rfl⟩ := hg
    apply hPs
    by_cases hP : P (𝒰.X i) (𝒰.f i)
    · exact hP
    · refine (hE _ _ ⟨fun a => ?_⟩).1
      have hb : 𝒰.f i a ∈ B := Set.mem_iUnion₂.2 ⟨i, hP, a, rfl⟩
      have ha : 𝒰.f i a ∈ A := by rw [h1]; trivial
      exact hdis _ ha hb

theorem res_id' {q : ℕ} {U : Scheme.{0}} (x : Sec (tw q 0) U) : Sec.res (𝟙 U) x = x := by
  simp only [Sec.res, op_id]
  rw [CategoryTheory.Functor.map_id]
  rfl

theorem res_sub' {q : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (a b : Sec (tw q 0) U) :
    Sec.res g (a - b) = Sec.res g a - Sec.res g b := map_sub _ _ _

theorem PtLift_of (hC : PtCov) : PtLift := by
  intro k _ _ X z R hR
  obtain ⟨Sv, hSv, hSs⟩ := hR
  have hpb : Sv.pullback z ∈ Scheme.etaleTopology (S k) := Scheme.etaleTopology.pullback_stable z hSv
  obtain ⟨T, hT, hTs⟩ := hC k (𝟙 (S k)) inferInstance (Sv.pullback z) hpb
  obtain ⟨𝒰, h𝒰⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hT
  have hne : Nonempty (S k) := inferInstance
  obtain ⟨i, -⟩ := ((Scheme.presieve₀_mem_precoverage_iff _).mp 𝒰.mem₀).1 (Classical.choice hne)
  obtain ⟨U, g', h, hg', -, w, hw⟩ := hTs _ (𝒰.f i) (h𝒰 _ _ (Presieve.ofArrows.mk i))
  refine ⟨U, g' ≫ z, w, hSs _ _ hg', ?_⟩
  rw [Category.comp_id] at hw
  rw [← Category.assoc, hw, Category.id_comp]

theorem tateTwistSection_constantOnPoints_of_connLoc_lift (hT : LateralTheory.EtaleFoundations.CongruenceLocalDecomposition.TwLoc) (hL : ConnLoc) (hP : PtLift) : EtaleTateTwistSectionConstantOnPointsOfConnectedProper := by
  intro l _ k _ _ hl j X p hp s hX y y'
  haveI : NeZero (l ^ j) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hq : ((l ^ j : ℕ) : k) ≠ 0 := by push_cast; exact pow_ne_zero _ hl
  obtain ⟨ζ0⟩ := primK k (l ^ j) hq
  let φ : k →+* Γ(X, ⊤) := (p.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  let v0 := Sec.res y.1 s
  let t := s - Sec.res p v0
  have key : ∀ z : Pt p, Sec.res z.1 t = Sec.res z.1 s - v0 := by
    intro z
    show Sec.res z.1 (s - Sec.res p v0) = _
    rw [res_sub', ← res_comp, z.2, res_id']
  have hne : Nonempty (S k) := inferInstance
  let P : ∀ V : Scheme.{0}, (V ⟶ X) → Prop := fun V g => ∀ (W : Scheme.{0}) (h : W ⟶ V), Nonempty W → Sec.res (h ≫ g) t = 0
  let Q : ∀ V : Scheme.{0}, (V ⟶ X) → Prop := fun V g => ∀ (W : Scheme.{0}) (h : W ⟶ V), Nonempty W → Sec.res (h ≫ g) t ≠ 0
  have hPs : ∀ (V W : Scheme.{0}) (g : V ⟶ X) (h : W ⟶ V), P V g → P W (h ≫ g) := by
    intro V W g h hg W' h' hW'
    rw [← Category.assoc]; exact hg W' (h' ≫ h) hW'
  have hQs : ∀ (V W : Scheme.{0}) (g : V ⟶ X) (h : W ⟶ V), Q V g → Q W (h ≫ g) := by
    intro V W g h hg W' h' hW'
    rw [← Category.assoc]; exact hg W' (h' ≫ h) hW'
  have hE : ∀ (V : Scheme.{0}) (g : V ⟶ X), IsEmpty V → P V g ∧ Q V g := by
    intro V g hV
    exact ⟨fun W h hW => (hV.false (h.base (Classical.choice hW))).elim,
      fun W h hW => (hV.false (h.base (Classical.choice hW))).elim⟩
  have hD : ∀ (V : Scheme.{0}) (g : V ⟶ X), P V g → Q V g → IsEmpty V := by
    intro V g hPg hQg
    by_contra hV
    rw [not_isEmpty_iff] at hV
    exact hQg V (𝟙 V) hV (hPg V (𝟙 V) hV)
  have hPQ : Loc X (fun V g => P V g ∨ Q V g) := by
    obtain ⟨Sv, hSv, hSs⟩ := (hT (l ^ j) 0).1 X (ζ0.map φ) t
    refine ⟨Sv, hSv, fun V g hg => ?_⟩
    obtain ⟨c, hc⟩ := hSs V g hg
    by_cases hqc : l ^ j ∣ c
    · left
      intro W h _
      rw [res_comp, hc, res_nsmul]
      obtain ⟨m, rfl⟩ := hqc
      rw [mul_comm]
      first
        | (rw [mul_nsmul, q_nsmul, nsmul_zero])
        | (rw [mul_nsmul', q_nsmul, nsmul_zero])
        | (rw [mul_nsmul', q_nsmul, smul_zero])
        | (rw [mul_nsmul, q_nsmul, smul_zero])
    · right
      intro W h hW hz
      haveI := hW
      apply hqc
      rw [res_comp, hc, res_nsmul, (hT (l ^ j) 0).2.2] at hz
      exact (hT (l ^ j) 0).2.1 W _ c hz
  have hy0 : Sec.res y.1 t = 0 := by rw [key]; exact sub_self _
  rcases hL hX P Q hPs hQs hE hD hPQ with hLP | hLQ
  · obtain ⟨V, g, w, hg, hw⟩ := hP k y'.1 P hLP
    have h1 := hg (S k) w hne
    rw [hw, key, sub_eq_zero] at h1
    exact h1.symm
  · obtain ⟨V, g, w, hg, hw⟩ := hP k y.1 Q hLQ
    exact absurd (by rw [hw]; exact hy0) (hg (S k) w hne)

theorem tateTwistSection_constantOnPoints_of_twLoc_ptCov (hT : LateralTheory.EtaleFoundations.CongruenceLocalDecomposition.TwLoc) (hC : PtCov) : EtaleTateTwistSectionConstantOnPointsOfConnectedProper :=
  tateTwistSection_constantOnPoints_of_connLoc_lift hT ConnLoc_pf (PtLift_of hC)

end LateralTheory.EtaleTrace
end
end

section -- merged from Development.EtaleCohomology.EtaleTrace.PtCovPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.EtaleTrace

theorem exists_ratPt_of_etale (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} (p : X ⟶ S k)
    (hp : IsProper p) {U : Scheme.{0}} (f : U ⟶ X) [Etale f] (x : U) :
    ∃ w : S k ⟶ U, w ≫ f ≫ p = 𝟙 _ := by
  have := hp
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  have hopen : IsOpen (Set.range f) := f.isOpenMap.isOpen_range
  obtain ⟨y, ⟨x', rfl⟩, hy⟩ := nonempty_inter_closedPoints (show (Set.range f).Nonempty from ⟨f x, x, rfl⟩) hopen.isLocallyClosed
  let s : S k ⟶ X := pointOfClosedPoint p (f x') hy
  obtain ⟨l, hl, -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed f s x' (pointOfClosedPoint_apply p (f x') hy _).symm
  exact ⟨l, by rw [reassoc_of% hl]; exact pointOfClosedPoint_comp p (f x') hy⟩

theorem PtCov_of : PtCov := by
  intro k _ _ X p hp Sv hSv
  obtain ⟨𝒰, h𝒰⟩ := Scheme.mem_grothendieckTopology_iff.1 hSv
  let T : Sieve X :=
    { arrows := fun V g => ∃ (U : Scheme.{0}) (g' : U ⟶ X) (h : V ⟶ U),
        Sv.arrows g' ∧ h ≫ g' = g ∧ ∃ w : S k ⟶ U, w ≫ g' ≫ p = 𝟙 _
      downward_closed := by
        rintro V W g ⟨U, g', h, hg', rfl, w, hw⟩ a
        exact ⟨U, g', a ≫ h, hg', by simp, w, hw⟩ }
  refine ⟨T, ?_, fun V g hg => hg⟩
  have hG : Sieve.generate (Presieve.ofArrows 𝒰.X 𝒰.f) ∈ Scheme.etaleTopology X :=
    Scheme.mem_grothendieckTopology_iff.2 ⟨𝒰, Sieve.le_generate _⟩
  refine (Scheme.etaleTopology).transitive hG T ?_
  rintro Z _ ⟨W, a, b, hb, rfl⟩
  rw [Sieve.pullback_comp]
  refine (Scheme.etaleTopology).pullback_stable a ?_
  obtain ⟨i⟩ := hb
  by_cases hne : Nonempty (𝒰.X i)
  · obtain ⟨x⟩ := hne
    obtain ⟨w, hw⟩ := exists_ratPt_of_etale k p hp (𝒰.f i) x
    have : T.arrows (𝒰.f i) := ⟨𝒰.X i, 𝒰.f i, 𝟙 _, h𝒰 _ _ (Presieve.ofArrows.mk i), by simp, w, hw⟩
    rw [Sieve.pullback_eq_top_of_mem T this]
    exact (Scheme.etaleTopology).top_mem _
  · have : IsEmpty (𝒰.X i) := not_nonempty_iff.1 hne
    exact (Scheme.etaleTopology).superset_covering bot_le (Scheme.bot_mem_grothendieckTopology _)

end LateralTheory.EtaleTrace
end
end

section -- merged from Development.EtaleCohomology.TateTwists.AlgPowPfR
noncomputable section
open Polynomial GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.AlgPowPf

theorem root_dom {K : Type} [CommRing K] [IsDomain K] (q : ℕ) [NeZero q] (hq : (q : K) ≠ 0) (z : K)
    (hz : aeval z (cyclotomic q ℤ) = 0) : IsPrimitiveRoot z q := by
  have : NeZero (q : K) := ⟨hq⟩
  have h : (cyclotomic q K).IsRoot z := by
    rw [IsRoot, ← map_cyclotomic_int, eval_map]
    simpa [aeval_def] using hz
  exact (isRoot_cyclotomic_iff).1 h

theorem eq_pow_dom {K : Type} [CommRing K] [IsDomain K] (q : ℕ) [NeZero q] (z x : K)
    (hz : IsPrimitiveRoot z q) (hx : IsPrimitiveRoot x q) : ∃ b : (ZMod q)ˣ, x = z ^ (b : ZMod q).val := by
  obtain ⟨i, hi, hzi⟩ := hz.eq_pow_of_pow_eq_one hx.pow_eq_one
  have hc : i.Coprime q := (hz.pow_iff_coprime (Nat.pos_of_ne_zero (NeZero.ne q)) i).1 (hzi ▸ hx)
  refine ⟨ZMod.unitOfCoprime i hc, ?_⟩
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi, hzi]

theorem pow_ne_dom {K : Type} [CommRing K] (q : ℕ) [NeZero q] (z : K)
    (hz : IsPrimitiveRoot z q) (a b : (ZMod q)ˣ) (h : a ≠ b) :
    z ^ (a : ZMod q).val ≠ z ^ (b : ZMod q).val := by
  intro e
  apply h
  exact Units.ext (ZMod.val_injective q (hz.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) e))

theorem pow_q {A : Type} [CommRing A] (q : ℕ) (z : A) (hz : aeval z (cyclotomic q ℤ) = 0) : z ^ q = 1 := by
  obtain ⟨p, hp⟩ := cyclotomic.dvd_X_pow_sub_one q ℤ
  have := congrArg (aeval z) hp
  simp [hz] at this
  exact sub_eq_zero.1 this

theorem self_sq {A : Type} [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) (x y : A)
    (hx : x ^ q = 1) (hy : y ^ q = 1) : ∃ w : A, x - y = (x - y) ^ 2 * w := by
  set d := x - y
  set u := ∑ i ∈ Finset.range q, x ^ i * y ^ (q - 1 - i)
  have hdu : u * d = 0 := by
    have := geom_sum₂_mul x y q
    rw [hx, hy, sub_self] at this
    exact this
  have hyu : IsUnit y := isUnit_iff_exists_inv.2 ⟨y ^ (q - 1), by rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero (NeZero.ne q)), hy]⟩
  set c : A := (q : A) * y ^ (q - 1)
  have hc : IsUnit c := hq.mul (hyu.pow _)
  have hmem : u - c ∈ Ideal.span {d} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have hxy : Ideal.Quotient.mk (Ideal.span {d}) x = Ideal.Quotient.mk (Ideal.span {d}) y := by
      rw [Ideal.Quotient.eq]; exact Ideal.subset_span rfl
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [u, c, map_sub, map_sum, map_mul, map_pow, map_natCast, hxy]
    rw [geom_sum₂_self, sub_self]
  obtain ⟨w0, hw0⟩ := Ideal.mem_span_singleton'.1 hmem
  obtain ⟨cu, hcu⟩ := hc
  refine ⟨-(w0 * ↑cu⁻¹), ?_⟩
  have hdc : d * c = -(d ^ 2 * w0) := by
    have : c = u - w0 * d := by rw [hw0]; ring
    rw [this]; linear_combination hdu
  calc d = d * c * ↑cu⁻¹ := by rw [← hcu, mul_assoc, Units.mul_inv, mul_one]
    _ = _ := by rw [hdc]; ring

theorem self_pow {A : Type} [CommRing A] (d w : A) (h : d = d ^ 2 * w) (k : ℕ) : d = d ^ (k + 1) * w ^ k := by
  induction k with
  | zero => simp
  | succ k ih => calc d = d ^ (k + 1) * w ^ k := ih
      _ = d ^ k * d * w ^ k := by ring
      _ = d ^ k * (d ^ 2 * w) * w ^ k := by rw [← h]
      _ = _ := by ring

theorem AlgPow_of : LateralTheory.EtaleFoundations.TwSecLocPf.AlgPow := by
  classical
  intro q _ A _ ζ ξ
  obtain ⟨hqA, hζ⟩ := ζ.2
  obtain ⟨-, hξ⟩ := ξ.2
  let f : (ZMod q)ˣ → A := fun a => ∏ b ∈ Finset.univ.erase a, (ξ.1 - ζ.1 ^ (b : ZMod q).val)

  have hdom : ∀ p : Ideal A, p.IsPrime → IsPrimitiveRoot (Ideal.Quotient.mk p ζ.1) q ∧
      IsPrimitiveRoot (Ideal.Quotient.mk p ξ.1) q := by
    intro p hp
    have hq : ((q : ℕ) : A ⧸ p) ≠ 0 := by
      have := hqA.map (Ideal.Quotient.mk p)
      rw [map_natCast] at this
      exact this.ne_zero
    have hm : ∀ z : A, aeval z (cyclotomic q ℤ) = 0 → aeval (Ideal.Quotient.mk p z) (cyclotomic q ℤ) = 0 := by
      intro z hz
      have := Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ ℤ p) z (cyclotomic q ℤ)
      rw [hz, map_zero] at this
      simpa using this
    exact ⟨root_dom q hq _ (hm _ hζ), root_dom q hq _ (hm _ hξ)⟩
  refine ⟨Set.range f, ?_, ?_⟩
  · by_contra hne
    obtain ⟨m, hm, hsm⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨h1, h2⟩ := hdom m hm.isPrime
    obtain ⟨b0, hb0⟩ := eq_pow_dom q _ _ h1 h2
    have hin : f b0 ∈ m := hsm (Ideal.subset_span ⟨b0, rfl⟩)
    rw [← Ideal.Quotient.eq_zero_iff_mem] at hin
    simp only [f, map_prod, map_sub, map_pow, hb0] at hin
    rw [Finset.prod_eq_zero_iff] at hin
    obtain ⟨b, hb, e⟩ := hin
    exact pow_ne_dom q _ h1 b0 b (Finset.ne_of_mem_erase hb).symm (sub_eq_zero.1 e)
  · rintro _ ⟨a, rfl⟩
    refine ⟨a, ?_⟩
    have hnil : IsNilpotent (f a * (ξ.1 - ζ.1 ^ (a : ZMod q).val)) := by
      rw [← mem_nilradical, nilradical_eq_sInf, Ideal.mem_sInf]
      intro p hp
      have hp : p.IsPrime := hp
      obtain ⟨h1, h2⟩ := hdom p hp
      obtain ⟨b0, hb0⟩ := eq_pow_dom q _ _ h1 h2
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simp only [f, map_mul, map_prod, map_sub, map_pow, hb0]
      by_cases hab : b0 = a
      · subst hab; simp
      · apply mul_eq_zero_of_left
        exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hab, Finset.mem_univ _⟩) (sub_self _)
    obtain ⟨n, hn⟩ := hnil
    obtain ⟨w, hw⟩ := self_sq q hqA ξ.1 (ζ.1 ^ (a : ZMod q).val) (pow_q q _ hξ)
      (by rw [← pow_mul, mul_comm, pow_mul, pow_q q _ hζ, one_pow])
    refine ⟨n, ?_⟩
    rw [self_pow _ w hw n, pow_succ, mul_pow] at *
    calc f a ^ n * ((ξ.1 - ζ.1 ^ (a : ZMod q).val) ^ n * (ξ.1 - ζ.1 ^ (a : ZMod q).val) * w ^ n)
        = (f a ^ n * (ξ.1 - ζ.1 ^ (a : ZMod q).val) ^ n) * ((ξ.1 - ζ.1 ^ (a : ZMod q).val) * w ^ n) := by ring
      _ = 0 := by rw [hn, zero_mul]

end LateralTheory.EtaleFoundations.AlgPowPf
end
end

section -- merged from Development.EtaleCohomology.TateTwists.TwTorsPfR
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.TwTorsPf

section Field
variable {q : ℕ} [NeZero q] {k : Type} [Field k]

theorem prim_isPrim (ζ : Prim q k) : IsPrimitiveRoot ζ.1 q := by
  haveI : NeZero (q : k) := ⟨ζ.2.1.ne_zero⟩
  rw [← Polynomial.isRoot_cyclotomic_iff]
  have h := ζ.2.2
  simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic] using h

theorem pow_eq_pow_cast {ζ : k} (h : IsPrimitiveRoot ζ q) {m n : ℕ} (e : ζ ^ m = ζ ^ n) :
    (m : ZMod q) = (n : ZMod q) := by
  have h0 : ζ ≠ 0 := h.ne_zero (NeZero.ne q)
  have e' : ζ ^ ((m : ℤ) - n) = 1 := by
    rw [zpow_sub₀ h0, zpow_natCast, zpow_natCast, e, div_self (pow_ne_zero _ h0)]
  have hd := (h.zpow_eq_one_iff_dvd _).1 e'
  have := (ZMod.intCast_eq_intCast_iff_dvd_sub (n : ℤ) (m : ℤ) q).2 hd
  exact_mod_cast this.symm
end Field

section Field2
variable {q : ℕ} [NeZero q] {k : Type} [Field k]

def ex (ζ0 ξ : Prim q k) : ℕ :=
  ((prim_isPrim ζ0).eq_pow_of_pow_eq_one (prim_isPrim ξ).pow_eq_one).choose

theorem ex_spec (ζ0 ξ : Prim q k) : ζ0.1 ^ ex ζ0 ξ = ξ.1 :=
  ((prim_isPrim ζ0).eq_pow_of_pow_eq_one (prim_isPrim ξ).pow_eq_one).choose_spec.2

theorem ex_cop (ζ0 ξ : Prim q k) : (ex ζ0 ξ).Coprime q := by
  have h := prim_isPrim ξ
  rw [← ex_spec ζ0 ξ] at h
  exact ((prim_isPrim ζ0).pow_iff_coprime (Nat.pos_of_ne_zero (NeZero.ne q)) _).1 h

theorem ex_eq (ζ0 ξ : Prim q k) {m : ℕ} (h : ζ0.1 ^ m = ξ.1) : (ex ζ0 ξ : ZMod q) = m :=
  pow_eq_pow_cast (prim_isPrim ζ0) ((ex_spec ζ0 ξ).trans h.symm)

def exU (ζ0 ξ : Prim q k) : (ZMod q)ˣ := ZMod.unitOfCoprime _ (ex_cop ζ0 ξ)

theorem exU_rel (ζ0 η ξ : Prim q k) (a : (ZMod q)ˣ) (h : ξ.1 = η.1 ^ (a : ZMod q).val) :
    exU ζ0 ξ = exU ζ0 η * a := by
  ext
  simp only [exU, ZMod.coe_unitOfCoprime, Units.val_mul]
  rw [ex_eq ζ0 ξ (m := ex ζ0 η * (a : ZMod q).val)]
  · push_cast
    rw [ZMod.natCast_zmod_val]
  · rw [pow_mul, ex_spec, h]

theorem exU_self (ζ0 : Prim q k) : exU ζ0 ζ0 = 1 := by
  ext
  simp only [exU, ZMod.coe_unitOfCoprime, Units.val_one]
  rw [ex_eq ζ0 ζ0 (m := 1) (pow_one _)]
  simp

def val (i : ℤ) (ζ0 ξ : Prim q k) : ULift.{1} (ZMod q) := ULift.up (((exU ζ0 ξ) ^ i : (ZMod q)ˣ) : ZMod q)

def fn (i : ℤ) (ζ0 : Prim q k) : (Prim q k →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q) :=
  Finsupp.linearCombination _ (val i ζ0)

theorem rel_le (i : ℤ) (ζ0 : Prim q k) : twRel q i k ≤ LinearMap.ker (fn i ζ0) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨η, ξ, a, h, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, fn, Finsupp.linearCombination_single]
  rw [sub_eq_zero, val, val, exU_rel ζ0 η ξ a h, mul_zpow]
  apply ULift.ext
  simp [mul_comm]

theorem field_tors (i : ℤ) (ζ : Prim q k) (c : ℕ)
    (h : c • (Submodule.Quotient.mk (Finsupp.single ζ 1) : (Prim q k →₀ ULift.{1} (ZMod q)) ⧸ twRel q i k) = 0) :
    q ∣ c := by
  have h2 := congrArg ((twRel q i k).liftQ (fn i ζ) (rel_le i ζ)) h
  rw [map_nsmul, map_zero, Submodule.liftQ_apply, fn, Finsupp.linearCombination_single, val, exU_self] at h2
  have h3 := congrArg ULift.down h2
  simp at h3
  exact (ZMod.natCast_eq_zero_iff c q).1 (by simpa using h3)
end Field2

theorem twF_map_mk {q : ℕ} (i : ℤ) {A B : CommRingCat.{0}} (φ : A ⟶ B) (ζ : Prim q A) :
    ((twF q i).map φ).hom (Submodule.Quotient.mk (Finsupp.single ζ 1)) =
      Submodule.Quotient.mk (Finsupp.single (ζ.map φ.hom) 1) := by
  change Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map φ.hom) (Finsupp.single ζ 1)) = _
  rw [Finsupp.mapDomain_single]

theorem ring_tors {q : ℕ} [NeZero q] (i : ℤ) {A : Type} [CommRing A] [Nontrivial A] (ζ : Prim q A) (c : ℕ)
    (h : c • (Submodule.Quotient.mk (Finsupp.single ζ 1) : (Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) = 0) :
    q ∣ c := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  let f : A →+* A ⧸ m := Ideal.Quotient.mk m
  have h2 := congrArg (Submodule.mapQ _ _ (Finsupp.lmapDomain (ULift.{1} (ZMod q)) (ULift.{1} (ZMod q)) (Prim.map f))
    (twRel_le q i f)) h
  rw [map_nsmul, map_zero, Submodule.mapQ_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single] at h2
  exact field_tors i (ζ.map f) c h2

theorem jsEt : Scheme.JointlySurjective (Scheme.precoverage @AlgebraicGeometry.Etale.{0}) where
  exists_eq {X} R := fun ⟨hR, _⟩ x ↦ by
    rw [Scheme.jointlySurjectivePrecoverage, Presieve.mem_comap_jointlySurjectivePrecoverage_iff] at hR
    obtain ⟨Y, g, hg, heq⟩ := hR x
    exact ⟨Y, g, hg, heq⟩

theorem TwTors_of : LateralTheory.EtaleFoundations.TwLocPf.TwTors := by
  intro q _ i U _ ζ c hc
  let P := Scheme.Γ ⋙ twF q i
  let x : P.obj (op U) := Submodule.Quotient.mk (Finsupp.single ζ 1)
  have h1 : (toSheafify Scheme.etaleTopology P).app (op U) (c • x) =
      (toSheafify Scheme.etaleTopology P).app (op U) 0 := by
    have : ((toSheafify Scheme.etaleTopology P).app (op U)).hom (c • x) = 0 := by
      rw [map_nsmul]; exact hc
    simpa using this
  have hS := Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) (c • x) 0 h1
  obtain ⟨𝒰, hle⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hS
  haveI := jsEt
  obtain ⟨j, y, -⟩ := 𝒰.exists_eq (Classical.arbitrary U)
  have hj := hle _ _ (Presieve.ofArrows.mk j)
  simp only [Presheaf.equalizerSieve_apply, map_zero] at hj
  have : Nonempty (𝒰.X j) := ⟨y⟩
  have : Nonempty (⊤ : (𝒰.X j).Opens) := ⟨⟨y, trivial⟩⟩
  have h3 : ((twF q i).map (𝒰.f j).appTop).hom (c • x) = 0 := hj
  have h4 : c • ((twF q i).map (𝒰.f j).appTop).hom (Submodule.Quotient.mk (Finsupp.single ζ 1)) = 0 :=
    (map_nsmul ((twF q i).map (𝒰.f j).appTop).hom c _).symm.trans h3
  rw [twF_map_mk] at h4
  exact ring_tors i _ c h4

end LateralTheory.EtaleFoundations.TwTorsPf
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace CochainComplex.HomComplex

namespace UpperTheory.Gal.KunnethLefschetz

private theorem twLoc : LateralTheory.EtaleFoundations.CongruenceLocalDecomposition.TwLoc :=
  LateralTheory.EtaleFoundations.TwLocPf.TwLoc_of
    (LateralTheory.EtaleFoundations.TwSecLocPf.TwSecLoc_of_alg LateralTheory.EtaleFoundations.AlgPowPf.AlgPow_of)
    LateralTheory.EtaleFoundations.TwTorsPf.TwTors_of

private theorem twZero : TwZero := TwZero_of_split twLoc PrimSplit_of

private theorem lowSec : EtaleTateTwistSectionsDeterminedByPointsOfProper := tateTwistSections_determinedByPoints_of_constant twLoc PtCov_of (tateTwistSection_constantOnPoints_of_twLoc_ptCov twLoc PtCov_of)

private theorem exists_ofRings_sec_eq_twF_zero (k : Type) [Field k] [IsAlgClosed k] (q : ℕ) (s : Sec (tw q 0) (S k)) :
    ∃ t, ofRings.sec (twF q 0) (S k) t = s := by
  have h := Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q 0)) s
  obtain ⟨t, ht⟩ := PtCover_of k _ h
  refine ⟨t, ht.trans ?_⟩
  simp
  rfl

private theorem ofRings_sec_twF_zero_injective (k : Type) [Field k] [IsAlgClosed k] (q : ℕ)
    (t1 t2 : ToType ((Scheme.Γ ⋙ twF q 0).obj (Opposite.op (S k))))
    (h : ofRings.sec (twF q 0) (S k) t1 = ofRings.sec (twF q 0) (S k) t2) : t1 = t2 := by
  have h2 := Presheaf.equalizerSieve_mem Scheme.etaleTopology
    (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q 0)) t1 t2 h
  have h3 := PtCover_of k _ h2
  have h4 : (Scheme.Γ ⋙ twF q 0).map (𝟙 (Opposite.op (S k))) t1 =
      (Scheme.Γ ⋙ twF q 0).map (𝟙 (Opposite.op (S k))) t2 := h3
  rwa [CategoryTheory.Functor.map_id, ModuleCat.id_apply, ModuleCat.id_apply] at h4

private theorem res_twGen_zero_eq_twGen_prim_map {q : ℕ} {U V : Scheme.{0}} (x : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res x (twGen 0 ζ) = twGen 0 (Prim.map (Scheme.Γ.map x.op).hom ζ) := by
  have hn := congrArg (fun φ => (ModuleCat.Hom.hom φ)
    (Submodule.Quotient.mk (Finsupp.single ζ 1) : (Scheme.Γ ⋙ twF q 0).obj (Opposite.op U)))
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q 0)).naturality x.op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hn
  refine hn.symm.trans ?_
  refine congrArg (ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q 0)).app (Opposite.op V))) ?_
  exact congrArg Submodule.Quotient.mk Finsupp.mapDomain_single

private theorem exists_nsmul_eq_of_single_one_eq {q : ℕ} [NeZero q] {P N : Type*} [AddCommGroup N] [Module (ULift.{1, 0} (ZMod q)) N]
    (φ : (P →₀ ULift.{1, 0} (ZMod q)) →ₗ[ULift.{1, 0} (ZMod q)] N) (g0 : N)
    (h : ∀ ξ, φ (Finsupp.single ξ 1) = g0) (f : P →₀ ULift.{1, 0} (ZMod q)) :
    ∃ n : ℕ, φ f = n • g0 := by
  induction f using Finsupp.induction with
  | zero => exact ⟨0, by simp⟩
  | single_add ξ c g _ _ ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨c.down.val + n, ?_⟩
    have hc : c = ((c.down.val : ℕ) : ULift.{1, 0} (ZMod q)) := by
      apply ULift.ext
      rw [ULift.down_natCast, ZMod.natCast_zmod_val]
    calc φ (Finsupp.single ξ c + g) = c • g0 + n • g0 := by
          rw [map_add (f := _), ← Finsupp.smul_single_one, map_smul, h, hn]
      _ = (c.down.val + n) • g0 := by
          rw [add_nsmul, ← Nat.cast_smul_eq_nsmul (ULift.{1, 0} (ZMod q)) c.down.val, ← hc]

private theorem sec_res_sec_map_comm {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (k : V ⟶ U)
    (b : Sec F U) : Sec.res k (Sec.map φ b) = Sec.map φ (Sec.res k b) := by
  simp only [Sec.res, Sec.map]
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, φ.hom.naturality]

private theorem lowPt (hA : A9) (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k] (hl : (l : k) ≠ 0) (j : ℕ) :
    (∀ z : Ht (l ^ j) (sch.obj (S k)) 0 0, ∃ a : ℕ, z = a • one (l ^ j) (sch.obj (S k))) ∧
      ∀ a : ℕ, a • one (l ^ j) (sch.obj (S k)) = 0 → l ^ j ∣ a := by
  haveI : NeZero (l ^ j) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨_, e, _, he2⟩ := hA (ZMod (l ^ j)) (tw (l ^ j) 0)
  obtain ⟨ζ0⟩ := exists_prim l k hl j
  let φ : ((Prim (l ^ j) Γ(S k, ⊤)) →₀ ULift.{1, 0} (ZMod (l ^ j))) →ₗ[ULift.{1, 0} (ZMod (l ^ j))]
      Sec (tw (l ^ j) 0) (S k) :=
    (ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF (l ^ j) 0)).app
      (Opposite.op (S k)))).comp (twRel (l ^ j) 0 Γ(S k, ⊤)).mkQ
  have hone : one (l ^ j) (sch.obj (S k)) = e (S k) (twGen 0 ζ0) := by
    obtain ⟨α, hα, hev⟩ := he2 (S k) (twGen 0 ζ0)
    have hnat : ∀ (U : Scheme.{0}) (x : Sx (sch.obj (S k)) 0 U) (ζ : Prim (l ^ j) Γ(U, ⊤)),
        ev (α : Cochain _ _ 0) 0 0 (by simp) U x = resGen 0 ζ := by
      intro U x ζ
      rw [evNat (ZMod (l ^ j)) (tw (l ^ j) 0) (S k) U (α : Cochain _ _ 0) x, hev]
      refine (sec_res_sec_map_comm (resι (ZMod (l ^ j)) (tw (l ^ j) 0)) (x : U ⟶ S k) (twGen 0 ζ0)).trans ?_
      exact congrArg (Sec.map (resι (ZMod (l ^ j)) (tw (l ^ j) 0)))
        ((res_twGen_zero_eq_twGen_prim_map (x : U ⟶ S k) ζ0).trans (twZero (l ^ j) U _ ζ))
    have h1 := pick_spec (show ∃ c, (fun c => ∃ β : Cocycle ((chains (ZMod (l ^ j))).obj (sch.obj (S k)))
        (res (ZMod (l ^ j)) (tw (l ^ j) 0)) 0, CohomologyClass.mk β = c ∧
          ∀ (U : Scheme) (x : Sx (sch.obj (S k)) 0 U) (ζ : Prim (l ^ j) Γ(U, ⊤)),
            ev (β : Cochain _ _ 0) 0 0 (by simp) U x = resGen 0 ζ) c from ⟨_, α, hα, hnat⟩)
    obtain ⟨β, hβ, hβev⟩ := h1
    refine hβ.symm.trans ((congrArg CohomologyClass.mk (CocEq_of _ _ _ β α (fun U x => ?_))).trans hα)
    exact (hβev U x (Prim.map (Scheme.Γ.map x.op).hom ζ0)).trans (hnat U x _).symm
  refine ⟨fun z => ?_, fun a ha => ?_⟩
  · obtain ⟨t, ht⟩ := exists_ofRings_sec_eq_twF_zero k (l ^ j) ((e (S k)).symm z)
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (twRel (l ^ j) 0 Γ(S k, ⊤)) t
    obtain ⟨n, hn⟩ := exists_nsmul_eq_of_single_one_eq φ (twGen 0 ζ0)
      (fun ξ => (show φ (Finsupp.single ξ 1) = twGen 0 ζ0 from twZero (l ^ j) (S k) ξ ζ0)) f
    refine ⟨n, ?_⟩
    have hf : φ f = (e (S k)).symm z := ht
    rw [hone, ← map_nsmul, ← hn, hf, AddEquiv.apply_symm_apply]
  · rw [hone, ← map_nsmul] at ha
    have hs : a • twGen 0 ζ0 = (0 : Sec (tw (l ^ j) 0) (S k)) :=
      (e (S k)).injective (ha.trans (map_zero _).symm)
    have h3 : (Submodule.Quotient.mk (a • Finsupp.single ζ0 (1 : ULift.{1, 0} (ZMod (l ^ j)))) :
        (_ ⧸ twRel (l ^ j) 0 Γ(S k, ⊤))) = Submodule.Quotient.mk 0 :=
      ofRings_sec_twF_zero_injective k (l ^ j) _ _ (show φ (a • Finsupp.single ζ0 1) = φ 0 by
        rw [map_nsmul, map_zero]
        exact hs)
    have h4 := (Submodule.Quotient.mk_eq_zero _).1 (h3.trans (Submodule.Quotient.mk_zero _))
    let ψ := Finsupp.linearCombination (ULift.{1, 0} (ZMod (l ^ j)))
      (fun _ : Prim (l ^ j) Γ(S k, ⊤) => (1 : ULift.{1, 0} (ZMod (l ^ j))))
    have hker : twRel (l ^ j) 0 Γ(S k, ⊤) ≤ LinearMap.ker ψ := by
      rw [twRel, Submodule.span_le]
      rintro x ⟨ζ, ξ, b, -, rfl⟩
      simp [ψ]
      exact sub_self (1 : ULift.{1, 0} (ZMod (l ^ j)))
    have h5 : ψ (a • Finsupp.single ζ0 1) = 0 := hker h4
    have h6 : ((a : ZMod (l ^ j))) = 0 := by
      have := congrArg ULift.down h5
      simpa [ψ] using this
    exact (ZMod.natCast_eq_zero_iff a (l ^ j)).1 h6

theorem lowTL_holds : LowTL := by
  intro hIn l _ k _ _ hl j
  obtain ⟨_, e, he1, _⟩ := (In.a9 hIn) (ZMod (l ^ j)) (tw (l ^ j) 0)
  refine ⟨lowPt (In.a9 hIn) l k hl j, ?_⟩
  intro X p hp z
  have hz : ∀ y : Pt p, pull (ZMod (l ^ j)) (sch.map y.1) (tw (l ^ j) 0) 0 z =
      e (S k) (Sec.res y.1 ((e X).symm z)) := by
    intro y
    rw [← he1, AddEquiv.apply_symm_apply]
  obtain ⟨h1, h2⟩ := lowSec l k hl j p hp ((e X).symm z)
  refine ⟨fun hy => ?_, fun hc y y' => ?_⟩
  · have h0 : (e X).symm z = 0 :=
      h1 (fun y => (e (S k)).injective (by rw [← hz, hy y, map_zero]))
    have := congrArg (e X) h0
    rwa [AddEquiv.apply_symm_apply, map_zero] at this
  · rw [hz, hz, h2 hc y y']

end UpperTheory.Gal.KunnethLefschetz
