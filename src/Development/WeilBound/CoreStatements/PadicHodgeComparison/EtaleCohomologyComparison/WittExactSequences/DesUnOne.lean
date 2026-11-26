module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ResKill
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.PerfectoidProd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianSemidefiniteNullRadical

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ToPfFull
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TensorProduct GroundTheory.PAdicHodge CrystallineSemistableComparison.CH

universe w v u v' u' v'' u''

namespace CrystallineSemistableComparison.D

variable (l : ℕ) [Fact l.Prime]

theorem isRt_rt : IsRt l (rt l) ∧ rt l 0 = pFlat l := by
  refine ⟨fun k => ?_, ?_⟩
  · apply (iterateFrobeniusEquiv (Ob l) l k).injective
    have h1 : iterateFrobeniusEquiv (Ob l) l (k + 1) (rt l (k + 1)) = pFlat l := RingEquiv.apply_symm_apply _ _
    have h2 : iterateFrobeniusEquiv (Ob l) l k (rt l k) = pFlat l := RingEquiv.apply_symm_apply _ _
    rw [h2, ← h1, iterateFrobeniusEquiv_def, iterateFrobeniusEquiv_def, ← pow_mul, pow_succ']
  · change (iterateFrobeniusEquiv (Ob l) l 0).symm (pFlat l) = pFlat l
    rw [iterateFrobeniusEquiv_zero]; rfl

theorem toPf_full : (toPf l).Full ∧ (toPf l).Faithful := by
  refine ⟨⟨fun {A B} φ => ⟨⟨φ.hom.hom.toRingHom, RingHom.ext fun c => φ.hom.hom.commutes c⟩, ?_⟩⟩,
    ⟨fun {A B} f g h => ?_⟩⟩
  · exact InducedCategory.hom_ext (CommAlgCat.hom_ext (AlgHom.ext fun x => rfl))
  · have h' := congrArg (fun φ => φ.hom.hom.toRingHom) h
    exact PAlg.Hom.ext h'

end CrystallineSemistableComparison.D
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.CechTens
set_option autoImplicit false

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace CrystallineSemistableComparison.D

theorem test_of_pre : ∀ (p : ℕ) [Fact p.Prime] (B : Type) [CommRing B] (r : ℕ → B), Pf p B → IsRt p r → AIC B → VAL (r 0) → ∃ (T : Type) (_ : CommRing T) (g : B →+* T), Pf p T ∧ AIC T ∧ VAL (g (r 0)) ∧ IsAdicComplete (Ideal.span {g (r 0)}) T ∧ g (r 0) ∈ nonZeroDivisors T ∧ (∀ (M : ℕ) (y : T), ∃ x, y - g x ∈ Ideal.span {g (r 0) ^ M}) ∧ (∀ (M : ℕ) (x : B), g x ∈ Ideal.span {g (r 0) ^ M} → ∀ k, r k * x ∈ Ideal.span {r 0 ^ M}) ∧ ∀ (T₁ : Type) [CommRing T₁] (x : B →+* T₁), IsAdicComplete (Ideal.span {x (r 0)}) T₁ → x (r 0) ∈ nonZeroDivisors T₁ → ∃! ψ : T →+* T₁, ψ.comp g = x := by
  intro p _ B _ r hB hr h1 h2
  obtain ⟨B₁, _, q, hq, hB₁, hreg, hker, ha, hv⟩ := Leaf.tors_quot p B (r 0) hB
  obtain ⟨T, _, g, hg⟩ := Leaf.compl_ex B₁ (q (r 0))
  refine ⟨T, inferInstance, g.comp q, Leaf.compl_pf p B₁ T _ g hg hB₁, Leaf.compl_aic B₁ T _ g hg hreg (ha h1) (hv h2),
    Leaf.compl_val B₁ T _ g hg (hv h2), hg.compl, Leaf.compl_reg B₁ T _ g hg hreg, fun M y => ?_, fun M x hx k => ?_,
    fun T₁ _ x hc hx => ?_⟩
  · obtain ⟨x, hx⟩ := hg.surj M y
    obtain ⟨x, rfl⟩ := hq x
    exact ⟨x, hx⟩
  · obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (hg.inj M (q x) hx)
    obtain ⟨b, rfl⟩ := hq b
    have e : r 0 ^ 1 * (x - b * r 0 ^ M) = 0 := by
      rw [pow_one, ← hker, map_sub, map_mul, map_pow, hb, sub_self]
    have e' := ((Leaf.pf_facts p B hB).2.2.2.2 r hr).2.2 1 _ e k
    exact Ideal.mem_span_singleton'.2 ⟨r k * b, by linear_combination -e'⟩
  · let x₁ : B₁ →+* T₁ := q.liftOfSurjective hq ⟨x, fun a ha => by
      have := congrArg x ((hker a).1 ha)
      rw [map_mul, map_zero] at this
      exact (mul_left_mem_nonZeroDivisors_eq_zero_iff hx).1 this⟩
    have hx₁ : ∀ a, x₁ (q a) = x a := fun a => RingHom.liftOfSurjective_comp_apply _ _ _ a
    obtain ⟨ψ, hψ, hu⟩ := Leaf.compl_univ B₁ T _ g hg T₁ x₁ (by rw [hx₁]; exact hc)
    refine ⟨ψ, RingHom.ext fun a => (RingHom.congr_fun hψ (q a)).trans (hx₁ a), fun ψ' h' => hu ψ' (RingHom.ext fun a => ?_)⟩
    obtain ⟨a, rfl⟩ := hq a
    exact (RingHom.congr_fun h' a).trans (hx₁ a).symm

theorem cech_tens : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] (r : ℕ → R) (N : Type) [AddCommGroup N] [Module R N] (A : Type) [CommRing A] [Algebra R A](B : Type) [CommRing B] [Algebra A B] (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)] [∀ n, Algebra R (K n)] [∀ n, IsScalarTower R A (K n)] (ι : ∀ n, Fin n → (B →ₐ[A] K n)) (δ : ∀ n, Fin (n + 1) → (K n →ₐ[A] K (n + 1))), IsRt p r → (∀ a : R, a ≠ 0 → ∃ M : ℕ, a ∣ r 0 ^ M) → Pf p A → Pf p B → Cov p (fun k => algebraMap R A (r k)) B → (∀ n, IsWP (ι n)) → (∀ n k i, (δ n k).comp (ι n i) = ι (n + 1) (k.succAbove i)) → (∀ w : N ⊗[R] K 0, ((alt (δ 0)).restrictScalars R).lTensor N w = 0 → ∀ k, r k • w = 0) ∧ ∀ (n : ℕ) (w : N ⊗[R] K (n + 1)), ((alt (δ (n + 1))).restrictScalars R).lTensor N w = 0 → ∀ k, r k • w ∈ LinearMap.range (((alt (δ n)).restrictScalars R).lTensor N) := by
  intro p _ R _ _ _ r N _ _ A _ _ B _ _ K _ _ _ _ ι δ hr h1 hA hB hc hw hδ
  have hK : ∀ n, Pf p (K n) := fun n => Leaf.wp_pf p A B (K n) n (ι n) (hw n) hA hB
  have dd := Leaf.wp_dd A B K ι δ hw hδ
  obtain ⟨H, hH⟩ := Leaf.wp_htpy A B K ι δ hw hδ
  obtain ⟨e0, e1⟩ := Leaf.ami_exact p A B _ hA hc K (fun n => alt (δ n)) H hK dd hH
  have e1' : ∀ n z, ((alt (δ (n + 1))).restrictScalars R) z = 0 → ∀ k, r k • z ∈ LinearMap.range ((alt (δ n)).restrictScalars R) := by
    intro n z hz k
    obtain ⟨y, hy⟩ := e1 n z hz k
    exact ⟨y, hy.trans (algebraMap_smul A (r k) z)⟩
  have tor : ∀ n (a : R) (x : K n), a ≠ 0 → a • x = 0 → ∀ k, r k • x = 0 := by
    intro n a x ha hx k
    obtain ⟨M, c, hc⟩ := h1 a ha
    rw [Algebra.smul_def]
    refine ((Leaf.pf_facts p (K n) (hK n)).2.2.2.2 (fun k => algebraMap R (K n) (r k)) (fun k => by rw [← map_pow, hr k])).2.2 M x ?_ k
    rw [← map_pow, ← Algebra.smul_def, hc, mul_comm, mul_smul, hx, smul_zero]
  refine ⟨fun w hw k => ?_, fun n => Leaf.tens_exact p R r N _ _ _ _ _ _ ((alt (δ (n + 2))).restrictScalars R) hr
    (dd (n + 1)) (e1' n) (e1' (n + 1)) (tor _)⟩
  obtain ⟨y, hy⟩ := Leaf.tens_exact p R r N PUnit _ _ _ 0 _ ((alt (δ 1)).restrictScalars R) hr (dd 0)
    (fun z hz k => ⟨0, by rw [map_zero, ← algebraMap_smul A, e0 z hz k]⟩) (e1' 0) (tor _) w hw k
  rw [← hy, LinearMap.lTensor_zero, LinearMap.zero_apply]

theorem fin_step : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (r : ℕ → A) (𝓔 : Set (Set (MvPolynomial (Fin 3) A))), Pf p A → IsRt p r → (∀ E ∈ 𝓔, ∀ (B : Type) [CommRing B] [Algebra A B], Pf p B → ∃ (B₁ : Type) (_ : CommRing B₁) (_ : Algebra B B₁), Pf p B₁ ∧ Cov p (fun k => algebraMap A B (r k)) B₁ ∧ Pt ((algebraMap B B₁).comp (algebraMap A B)) E) → ∀ J : Set (Set (MvPolynomial (Fin 3) A)), J.Finite → J ⊆ 𝓔 → ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Pf p B ∧ Cov p r B ∧ ∀ E ∈ J, Pt (algebraMap A B) E := by
  intro p _ A _ r 𝓔 hA hr h J hJ
  induction J, hJ using Set.Finite.induction_on with
  | empty => exact fun _ => ⟨A, inferInstance, inferInstance, hA, (Leaf.cov_mono p A r).1, fun _ h => h.elim⟩
  | @insert E J _ _ ih =>
    intro hs
    obtain ⟨B, _, _, hB, hc, hp⟩ := ih fun x hx => hs (Or.inr hx)
    obtain ⟨B₁, _, _, hB₁, hc₁, hp₁⟩ := h E (hs (Or.inl rfl)) B hB
    let _ : Algebra A B₁ := ((algebraMap B B₁).comp (algebraMap A B)).toAlgebra
    have : IsScalarTower A B B₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
    refine ⟨B₁, inferInstance, inferInstance, hB₁, Leaf.cov_comp p A B B₁ r hA hB hr hc hc₁, ?_⟩
    rintro E' (rfl | h')
    · exact hp₁
    · obtain ⟨y, hy⟩ := hp E' h'
      refine ⟨algebraMap B B₁ ∘ y, fun q hq => ?_⟩
      have := congrArg (algebraMap B B₁) (hy q hq)
      rwa [MvPolynomial.eval₂_comp_left, map_zero] at this

end CrystallineSemistableComparison.D
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.PfFrom
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TensorProduct GroundTheory.PAdicHodge CrystallineSemistableComparison.CH

namespace CrystallineSemistableComparison.D

abbrev pfOb {R : Type} [CommRing R] {p : ℕ} (X : Type) [CommRing X] [Algebra R X] (h : Pf p X) : PfC p R :=
  ⟨CommAlgCat.of R X, h⟩

abbrev pfHom {R : Type} [CommRing R] {p : ℕ} {X Y : Type} [CommRing X] [Algebra R X] [CommRing Y] [Algebra R Y]
    {hX : Pf p X} {hY : Pf p Y} (φ : X →ₐ[R] Y) : pfOb (R := R) X hX ⟶ pfOb (R := R) Y hY :=
  ObjectProperty.homMk (CommAlgCat.ofHom φ)

abbrev pfFrom {R : Type} [CommRing R] {p : ℕ} (A : PfC p R) (B : Type) [CommRing B] [Algebra R B] [Algebra A.obj B]
    [IsScalarTower R A.obj B] (hB : Pf p B) : A ⟶ pfOb (R := R) B hB :=
  ObjectProperty.homMk (CommAlgCat.ofHom (IsScalarTower.toAlgHom R A.obj B))

end CrystallineSemistableComparison.D
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.TestOfPre
section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.SpanMap
set_option autoImplicit false

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace CrystallineSemistableComparison.D

open MvPolynomial (X C)

open MvPolynomial in
noncomputable def eqA {A : Type} [CommRing A] (P : Polynomial A) : Set (MvPolynomial (Fin 3) A) := {Polynomial.aeval (X 0) P}


open MvPolynomial in
noncomputable def eqB {A : Type} [CommRing A] (f g : A) : Set (MvPolynomial (Fin 3) A) :=
  {X 0 * X 0 - X 0, X 0 * C f - X 1 * C g, (1 - X 0) * C g - X 2 * C f}

theorem pt_eqA {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (P : Polynomial A) :
    Pt φ (eqA P) ↔ ∃ x, (P.map φ).IsRoot x := by
  have e : ∀ y : Fin 3 → B, MvPolynomial.eval₂ φ y (Polynomial.aeval (MvPolynomial.X 0) P) = (P.map φ).eval (y 0) := by
    intro y
    induction P using Polynomial.induction_on' with
    | add a b ha hb => simp [ha, hb]
    | monomial n a => simp [Polynomial.aeval_monomial]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y 0, (e y).symm.trans (hy _ rfl)⟩
  · rintro ⟨x, hx⟩
    exact ⟨fun _ => x, fun q hq => by rw [show q = _ from hq, e]; exact hx⟩

theorem pt_eqB {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (f g : A) :
    Pt φ (eqB f g) ↔ ∃ e : B, IsIdempotentElem e ∧ e * φ f ∈ Ideal.span {φ g} ∧ (1 - e) * φ g ∈ Ideal.span {φ f} := by
  constructor
  · rintro ⟨y, hy⟩
    have h1 := hy _ (Or.inl rfl)
    have h2 := hy _ (Or.inr (Or.inl rfl))
    have h3 := hy _ (Or.inr (Or.inr rfl))
    simp only [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, MvPolynomial.eval₂_C,
      MvPolynomial.eval₂_one, sub_eq_zero] at h1 h2 h3
    exact ⟨y 0, h1, Ideal.mem_span_singleton'.2 ⟨_, h2.symm⟩, Ideal.mem_span_singleton'.2 ⟨_, h3.symm⟩⟩
  · rintro ⟨e, h1, h2, h3⟩
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 h2
    obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 h3
    refine ⟨![e, u, v], ?_⟩
    rintro q (rfl | rfl | rfl) <;>
      simp [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul, hu, hv, h1.eq]

theorem root_map {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (h : AIC B) : AICm φ := by
  intro P hP hd
  rcases subsingleton_or_nontrivial B with _ | _
  · exact ⟨0, Subsingleton.elim _ _⟩
  · exact h _ (hP.map φ) (by rwa [hP.natDegree_map])

theorem span_map {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {π f g : A} {N : ℕ} (h : π ^ N ∈ Ideal.span {f, g}) :
    φ π ^ N ∈ Ideal.span {φ f, φ g} := by
  obtain ⟨a, b, e⟩ := Ideal.mem_span_pair.1 h
  exact Ideal.mem_span_pair.2 ⟨φ a, φ b, by rw [← map_pow, ← e, map_add (f := _), map_mul, map_mul]⟩

theorem cov_step : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (r : ℕ → A), Pf p A → IsRt p r → ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Pf p B ∧ Cov p r B ∧ AICm (algebraMap A B) ∧ VALm (r 0) (algebraMap A B) ∧ Splits p (r 0) (algebraMap A B) := by
  intro p _ A _ r hA hr
  let 𝓔 : Set (Set (MvPolynomial (Fin 3) A)) := {E | (∃ P : Polynomial A, P.Monic ∧ 0 < P.natDegree ∧ E = eqA P) ∨
    ∃ f g : A, (∃ N : ℕ, r 0 ^ N ∈ Ideal.span {f, g}) ∧ E = eqB f g}
  obtain ⟨B, _, _, hB, hc, hE, hs⟩ := Leaf.big_step p A r 𝓔 hA (fin_step p A r 𝓔 hA hr (by
    rintro E (⟨P, hP, hd, rfl⟩ | ⟨f, g, ⟨N, hN⟩, rfl⟩) B _ _ hB
    · rcases subsingleton_or_nontrivial B with _ | _
      · exact ⟨B, inferInstance, inferInstance, hB, (Leaf.cov_mono p B _).1, (pt_eqA _ _).2 ⟨0, Subsingleton.elim _ _⟩⟩
      · obtain ⟨B₁, _, _, h1, h2, x, hx⟩ := Leaf.cov_root p B (fun k => algebraMap A B (r k)) (P.map (algebraMap A B)) hB
          (hP.map _) (by rwa [hP.natDegree_map])
        refine ⟨B₁, inferInstance, inferInstance, h1, h2, (pt_eqA _ _).2 ⟨x, ?_⟩⟩
        rw [← Polynomial.map_map, Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def]
        exact hx
    · obtain ⟨B₁, _, _, h1, h2, e, u, v, he, hu, hv⟩ := cov_blow p B (fun k => algebraMap A B (r k)) (algebraMap A B f)
        (algebraMap A B g) N hB (fun k => by rw [← map_pow, hr k]) (span_map _ hN)
      exact ⟨B₁, inferInstance, inferInstance, h1, h2, (pt_eqB _ _ _).2
        ⟨e, he, Ideal.mem_span_singleton'.2 ⟨u, hu.symm⟩, Ideal.mem_span_singleton'.2 ⟨v, hv.symm⟩⟩⟩))
  refine ⟨B, inferInstance, inferInstance, hB, hc, fun P hP hd => (pt_eqA _ _).1 (hE _ (Or.inl ⟨P, hP, hd, rfl⟩)),
    fun f g h => (pt_eqB _ _ _).1 (hE _ (Or.inr ⟨f, g, h, rfl⟩)), fun T _ x hT h1 h2 => hs T x hT ?_⟩
  rintro E (⟨P, hP, hd, rfl⟩ | ⟨f, g, ⟨N, hN⟩, rfl⟩)
  · exact (pt_eqA _ _).2 (root_map x h1 P hP hd)
  · exact (pt_eqB _ _ _).2 (h2 _ _ ⟨N, span_map x hN⟩)

end CrystallineSemistableComparison.D
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ColimLift
set_option autoImplicit false

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace CrystallineSemistableComparison.D

theorem colim_lift : ∀ (A : Type) [CommRing A](G : ℕ → Type) [∀ n, CommRing (G n)] [∀ n, Algebra A (G n)] (f : ∀ n, G n →ₐ[A] G (n + 1))(L : Type) [CommRing L] [Algebra A L] (ι : ∀ n, G n →ₐ[A] L), IsColim f ι → ∀ (T : Type) [CommRing T] (y : ∀ n, G n →+* T), (∀ n x, y (n + 1) (f n x) = y n x) → ∃ z : L →+* T, ∀ n x, z (ι n x) = y n x := by
  intro A _ G _ _ f L _ _ ι hc T _ y hy
  rcases hc with ⟨h1, h2, h3⟩
  refine GlobalTheory.CompanionTheory.ColimLift.exists_lift_of_surj_ker (fun n => (f n).toRingHom) (fun n => (ι n).toRingHom)
    (fun n k x => tr f n k x) h1 (fun _ _ => rfl) (fun _ _ _ => rfl) h2 (fun n x hx => ?_) y hy
  obtain ⟨k, hk⟩ := h3 n 1 (fun _ => x) (fun _ => hx)
  exact ⟨k, hk 0⟩

end CrystallineSemistableComparison.D
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.TowerSeq
set_option autoImplicit false

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace CrystallineSemistableComparison.D

structure St (p : ℕ) {A : Type} [CommRing A] (r : ℕ → A) : Type 1 where
  G : Type
  [ring : CommRing G]
  [alg : Algebra A G]
  pf : Pf p G
  cov : Cov p r G

attribute [instance] St.ring St.alg

theorem St.next (p : ℕ) [Fact p.Prime] {A : Type} [CommRing A] {r : ℕ → A} (hA : Pf p A) (hr : IsRt p r) (s : St p r) :
    ∃ (s' : St p r) (f : s.G →ₐ[A] s'.G), AICm (f : s.G →+* s'.G) ∧ VALm (algebraMap A s.G (r 0)) (f : s.G →+* s'.G) ∧
      Splits p (algebraMap A s.G (r 0)) (f : s.G →+* s'.G) := by
  obtain ⟨B, _, _, hB, hc, h1, h2, h3⟩ := cov_step p s.G (fun k => algebraMap A s.G (r k)) s.pf
    (fun k => by rw [← map_pow, hr k])
  letI : Algebra A B := ((algebraMap s.G B).comp (algebraMap A s.G)).toAlgebra
  haveI : IsScalarTower A s.G B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact ⟨⟨B, hB, Leaf.cov_comp p A s.G B r hA s.pf hr s.cov hc⟩, IsScalarTower.toAlgHom A s.G B, h1, h2, h3⟩

theorem tower_seq : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (r : ℕ → A), Pf p A → IsRt p r → ∃ (G : ℕ → Type) (_ : ∀ n, CommRing (G n)) (_ : ∀ n, Algebra A (G n)) (f : ∀ n, G n →ₐ[A] G (n + 1)), (∀ n, Pf p (G n) ∧ Cov p r (G n) ∧ AICm (f n : G n →+* G (n + 1)) ∧ VALm (algebraMap A (G n) (r 0)) (f n : G n →+* G (n + 1)) ∧ Splits p (algebraMap A (G n) (r 0)) (f n : G n →+* G (n + 1))) ∧ Function.Bijective (algebraMap A (G 0)) := by
  intro p _ A _ r hA hr
  choose nx f h using St.next p hA hr
  let s : ℕ → St p r := fun n => Nat.rec ⟨A, hA, (Leaf.cov_mono p A r).1⟩ (fun _ t => nx t) n
  exact ⟨fun n => (s n).G, fun n => (s n).ring, fun n => (s n).alg, fun n => f (s n),
    fun n => ⟨(s n).pf, (s n).cov, h (s n)⟩, Function.bijective_id⟩

theorem cov_tower : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (r : ℕ → A), Pf p A → IsRt p r → ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Pf p B ∧ Cov p r B ∧ AIC B ∧ VAL (algebraMap A B (r 0)) ∧ Splits p (r 0) (algebraMap A B) := by
  intro p _ A _ r hA hr
  obtain ⟨G, _, _, f, h, h0⟩ := tower_seq p A r hA hr
  obtain ⟨L, _, _, ι, hι⟩ := Leaf.colim_ex A G f
  have hp := Leaf.colim_pf p A G f L ι hι
  have ht := Leaf.colim_test A (r 0) G f L ι hι (fun n => (h n).2.2.1) (fun n => (h n).2.2.2.1)
  refine ⟨L, inferInstance, inferInstance, hp.1 fun n => (h n).1, Leaf.cov_cmp p A L r fun m n a c hs => ?_, ht.1, ht.2, ?_⟩
  · obtain ⟨N, hN⟩ := hp.2 m n a c hs
    exact ⟨G N, inferInstance, inferInstance, (h N).2.1, hN⟩
  · intro T _ x hT h1 h2
    have step : ∀ n (y : {y : G n →+* T // y.comp (algebraMap A (G n)) = x}),
        ∃ y' : {y : G (n + 1) →+* T // y.comp (algebraMap A (G (n + 1))) = x}, ∀ z, y'.1 (f n z) = y.1 z := by
      intro n y
      obtain ⟨y', hy'⟩ := (h n).2.2.2.2 T y.1 hT h1 (by rw [← RingHom.comp_apply, y.2]; exact h2)
      have e : ∀ z, y' (f n z) = y.1 z := fun z => RingHom.congr_fun hy' z
      refine ⟨⟨y', RingHom.ext fun a => ?_⟩, e⟩
      rw [RingHom.comp_apply, ← (f n).commutes, e, ← RingHom.comp_apply, y.2]
    choose nx hnx using step
    let e0 := RingEquiv.ofBijective (algebraMap A (G 0)) h0
    let y : ∀ n, {y : G n →+* T // y.comp (algebraMap A (G n)) = x} := fun n =>
      Nat.rec ⟨x.comp e0.symm.toRingHom, RingHom.ext fun a => congrArg x (e0.symm_apply_apply a)⟩ (fun n t => nx n t) n
    obtain ⟨z, hz⟩ := colim_lift A G f L ι hι T (fun n => (y n).1) (fun n => hnx n (y n))
    refine ⟨z, RingHom.ext fun a => ?_⟩
    rw [RingHom.comp_apply, ← (ι 0).commutes, hz, ← RingHom.comp_apply, (y 0).2]

end CrystallineSemistableComparison.D
end

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial
namespace CrystallineSemistableComparison.D.Leaf

theorem cov_tower : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (r : ℕ → A), Pf p A → IsRt p r → ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Pf p B ∧ Cov p r B ∧ AIC B ∧ VAL (algebraMap A B (r 0)) ∧ Splits p (r 0) (algebraMap A B) := CrystallineSemistableComparison.D.cov_tower

theorem test_of_pre : ∀ (p : ℕ) [Fact p.Prime] (B : Type) [CommRing B] (r : ℕ → B), Pf p B → IsRt p r → AIC B → VAL (r 0) → ∃ (T : Type) (_ : CommRing T) (g : B →+* T), Pf p T ∧ AIC T ∧ VAL (g (r 0)) ∧ IsAdicComplete (Ideal.span {g (r 0)}) T ∧ g (r 0) ∈ nonZeroDivisors T ∧ (∀ (M : ℕ) (y : T), ∃ x, y - g x ∈ Ideal.span {g (r 0) ^ M}) ∧ (∀ (M : ℕ) (x : B), g x ∈ Ideal.span {g (r 0) ^ M} → ∀ k, r k * x ∈ Ideal.span {r 0 ^ M}) ∧ ∀ (T₁ : Type) [CommRing T₁] (x : B →+* T₁), IsAdicComplete (Ideal.span {x (r 0)}) T₁ → x (r 0) ∈ nonZeroDivisors T₁ → ∃! ψ : T →+* T₁, ψ.comp g = x := CrystallineSemistableComparison.D.test_of_pre

theorem cech_tens : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] (r : ℕ → R) (N : Type) [AddCommGroup N] [Module R N] (A : Type) [CommRing A] [Algebra R A](B : Type) [CommRing B] [Algebra A B] (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)] [∀ n, Algebra R (K n)] [∀ n, IsScalarTower R A (K n)] (ι : ∀ n, Fin n → (B →ₐ[A] K n)) (δ : ∀ n, Fin (n + 1) → (K n →ₐ[A] K (n + 1))), IsRt p r → (∀ a : R, a ≠ 0 → ∃ M : ℕ, a ∣ r 0 ^ M) → Pf p A → Pf p B → Cov p (fun k => algebraMap R A (r k)) B → (∀ n, IsWP (ι n)) → (∀ n k i, (δ n k).comp (ι n i) = ι (n + 1) (k.succAbove i)) → (∀ w : N ⊗[R] K 0, ((alt (δ 0)).restrictScalars R).lTensor N w = 0 → ∀ k, r k • w = 0) ∧ ∀ (n : ℕ) (w : N ⊗[R] K (n + 1)), ((alt (δ (n + 1))).restrictScalars R).lTensor N w = 0 → ∀ k, r k • w ∈ LinearMap.range (((alt (δ n)).restrictScalars R).lTensor N) := CrystallineSemistableComparison.D.cech_tens

end CrystallineSemistableComparison.D.Leaf
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.DesTens
section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.PowersGood
section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.SplitClause
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TensorProduct GroundTheory.PAdicHodge CrystallineSemistableComparison.CH

namespace CrystallineSemistableComparison.D

variable (l : ℕ) [Fact l.Prime]

theorem split_clause (A : PfC l (Ob l)) (B : Type) [CommRing B] [Algebra (Ob l) B] [Algebra A.obj B]
    [IsScalarTower (Ob l) A.obj B] (hB : Pf l B) (hS : Splits l (algebraMap (Ob l) A.obj (rt l 0)) (algebraMap A.obj B)) :
    ∀ (t : Test l) (x : A ⟶ (testι l ⋙ toPf l).obj t), ∃ y : pfOb (R := Ob l) B hB ⟶ (testι l ⋙ toPf l).obj t, pfFrom A B hB ≫ y = x := by
  intro t x
  let xa : A.obj →ₐ[Ob l] t.obj.A := x.hom.hom
  have hPf : Pf l t.obj.A := ⟨t.obj.natCast_l, t.obj.perf.bijective_frobenius⟩
  have hV : VAL ((xa : A.obj →+* t.obj.A) (algebraMap (Ob l) A.obj (rt l 0))) := by
    have e : (xa : A.obj →+* t.obj.A) (algebraMap (Ob l) A.obj (rt l 0)) = t.obj.pi := by
      change xa (algebraMap (Ob l) A.obj (rt l 0)) = t.obj.s (pFlat l)
      rw [xa.commutes, ← (isRt_rt l).2]; rfl
    rw [e]; exact t.property.2
  obtain ⟨y, hy⟩ := hS t.obj.A (xa : A.obj →+* t.obj.A) hPf t.property.1 hV
  let ya : B →ₐ[Ob l] t.obj.A :=
    { y with
      commutes' := fun c => by
        change y (algebraMap (Ob l) B c) = algebraMap (Ob l) t.obj.A c
        rw [IsScalarTower.algebraMap_apply (Ob l) A.obj B c, ← RingHom.comp_apply, hy]
        exact xa.commutes c }
  refine ⟨ObjectProperty.homMk (CommAlgCat.ofHom ya), ?_⟩
  apply ObjectProperty.hom_ext
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro a
  change y (algebraMap A.obj B a) = xa a
  exact RingHom.congr_fun hy a

theorem test_clause (N : Type) [AddCommGroup N] [Module (Ob l) N] (M : ℕ) (hN : ∀ x : N, pFlat l ^ M • x = 0)
    (B : Type) [CommRing B] [Algebra (Ob l) B] (hB : Pf l B) (hA : AIC B) (hV : VAL (algebraMap (Ob l) B (rt l 0))) :
    ∃ (t₀ : Test l) (g : pfOb (R := Ob l) B hB ⟶ (testι l ⋙ toPf l).obj t₀),
      (∀ (t : Test l) (y : pfOb (R := Ob l) B hB ⟶ (testι l ⋙ toPf l).obj t), ∃! φ : t₀ ⟶ t, g ≫ (testι l ⋙ toPf l).map φ = y) ∧
      Almost (Ideal.span (Set.range (rt l))) ((tensF l (Ob l) N).map g).hom := by
  have hr := isRt_rt l
  have hIsRt : IsRt l (fun k => algebraMap (Ob l) B (rt l k)) := fun k => by
    simp only; rw [← map_pow, hr.1 k]
  obtain ⟨T, _, g, hPf, hAIC, hVAL, hcompl, hnzd, hsurj, hinj, huniv⟩ :=
    Leaf.test_of_pre l B (fun k => algebraMap (Ob l) B (rt l k)) hB hIsRt hA hV
  let s : Ob l →+* T := g.comp (algebraMap (Ob l) B)
  have hs0 : s (pFlat l) = g (algebraMap (Ob l) B (rt l 0)) := by
    simp only [s, RingHom.comp_apply, hr.2]
  letI : Algebra (Ob l) T := s.toAlgebra
  let P0 : PAlg l :=
    { A := T, s := s, perf := ⟨hPf.bij⟩
      compl := by rw [hs0]; exact hcompl
      tf := by rw [hs0]; exact hnzd }
  let t₀ : Test l := ⟨P0, hAIC, by show VAL (s (pFlat l)); rw [hs0]; exact hVAL⟩
  let gA : B →ₐ[Ob l] T := { g with commutes' := fun _ => rfl }
  let g' : pfOb (R := Ob l) B hB ⟶ (testι l ⋙ toPf l).obj t₀ := ObjectProperty.homMk (CommAlgCat.ofHom gA)
  refine ⟨t₀, g', ?_, ?_⟩
  · intro t y
    let ya : B →ₐ[Ob l] t.obj.A := y.hom.hom
    have hc : (ya : B →+* t.obj.A) (algebraMap (Ob l) B (rt l 0)) = t.obj.s (pFlat l) := by
      change ya (algebraMap (Ob l) B (rt l 0)) = _
      rw [ya.commutes, hr.2]; rfl
    obtain ⟨ψ, hψ, huq⟩ := huniv t.obj.A (ya : B →+* t.obj.A) (by rw [hc]; exact t.obj.compl) (by rw [hc]; exact t.obj.tf)
    have hcomm : ψ.comp P0.s = t.obj.s := by
      ext c
      change ψ (g (algebraMap (Ob l) B c)) = t.obj.s c
      rw [← RingHom.comp_apply ψ g, hψ]
      exact ya.commutes c
    refine ⟨ObjectProperty.homMk (⟨ψ, hcomm⟩ : PAlg.Hom P0 t.obj), ?_, ?_⟩
    · apply ObjectProperty.hom_ext
      apply CommAlgCat.hom_ext
      apply AlgHom.ext
      intro b
      change ψ (g b) = ya b
      exact RingHom.congr_fun hψ b
    · intro φ hφ
      apply ObjectProperty.hom_ext
      apply PAlg.Hom.ext
      apply huq
      ext b
      have := congrArg (fun u => u.hom.hom b) hφ
      exact this
  · have key : ((tensF l (Ob l) N).map g').hom = gA.toLinearMap.lTensor N := rfl
    obtain ⟨hsT, hkT⟩ := Leaf.tens_compl (Ob l) (rt l) M N B T gA (by rw [hr.2]; exact hN)
      (fun y => hsurj M y) (fun x hx k => by rw [Algebra.smul_def]; exact hinj M x hx k)
    rw [key]
    intro a ha
    refine ⟨?_, fun y => ?_⟩
    · induction ha using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨k, rfl⟩ := hx
        intro w hw; exact hkT w hw k
      | zero => intro w _; exact zero_smul _ _
      | add x y _ _ hx hy => intro w hw; rw [add_smul, hx w hw, hy w hw, add_zero]
      | smul c x _ hx => intro w hw; rw [smul_eq_mul, mul_smul, hx w hw, smul_zero]
    · exact hsT (a • y)

end CrystallineSemistableComparison.D
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ExactUpToSpan
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TensorProduct GroundTheory.PAdicHodge CrystallineSemistableComparison.CH

universe v' u'

namespace CrystallineSemistableComparison.D

section Abs

variable {R : Type} [CommRing R] {p : ℕ}

theorem pf_ext {X Y : PfC p R} {f g : X ⟶ Y} (h : ∀ x, f.hom.hom x = g.hom.hom x) : f = g :=
  ObjectProperty.hom_ext _ (CommAlgCat.hom_ext (AlgHom.ext h))

theorem injUpTo_span {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] (S : Set R)
    (f : M →ₗ[R] N) (h : ∀ s ∈ S, InjUpTo s f) : ∀ s ∈ Ideal.span S, InjUpTo s f := by
  intro s hs
  induction hs using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => intro z _; exact zero_smul R z
  | add x y _ _ hx hy => intro z hz; rw [add_smul, hx z hz, hy z hz, add_zero]
  | smul a x _ hx => intro z hz; rw [smul_eq_mul, mul_smul, hx z hz, smul_zero]

theorem exactUpTo_span {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module R M] [Module R N]
    [Module R P] (S : Set R) (f : M →ₗ[R] N) (g : N →ₗ[R] P) (h : ∀ s ∈ S, ExactUpTo s f g) :
    ∀ s ∈ Ideal.span S, ExactUpTo s f g := by
  intro s hs
  induction hs using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => intro z _; exact ⟨0, by rw [map_zero, zero_smul]⟩
  | add x y _ _ hx hy =>
    intro z hz
    obtain ⟨u, hu⟩ := hx z hz
    obtain ⟨v, hv⟩ := hy z hz
    exact ⟨u + v, by rw [map_add (f := _), hu, hv, add_smul]⟩
  | smul a x _ hx =>
    intro z hz
    obtain ⟨u, hu⟩ := hx z hz
    exact ⟨a • u, by rw [map_smul, hu, smul_eq_mul, mul_smul]⟩

variable {T : Type u'} [Category.{v'} T] (j : T ⥤ PfC p R)
variable (A : PfC p R) (B : Type) [CommRing B] [Algebra R B] [Algebra A.obj B] [IsScalarTower R A.obj B] (hB : Pf p B)
  (K : ℕ → Type) [∀ n, CommRing (K n)] [∀ n, Algebra R (K n)] [∀ n, Algebra A.obj (K n)] [∀ n, IsScalarTower R A.obj (K n)]
  (hK : ∀ n, Pf p (K n)) (ι : ∀ n, Fin n → (B →ₐ[A.obj] K n)) (hι : ∀ n, IsWP (ι n))
  (δ : ∀ n, Fin (n + 1) → (K n →ₐ[A.obj] K (n + 1)))
  (hδ : ∀ n k i, (δ n k).comp (ι n i) = ι (n + 1) (k.succAbove i))
  (hrel : ∀ (n : ℕ) (k : Fin (n + 2)) (i : Fin (n + 1)),
    (δ (n + 1) (k.succAbove i)).comp (δ n (i.predAbove k)) = (δ (n + 1) k).comp (δ n i))
  (h0 : Function.Bijective (algebraMap A.obj (K 0))) (h1 : Function.Bijective (ι 1 0))

def univMap (n : ℕ) (X : PfC p R) (x : A ⟶ X) (y : Fin n → (pfOb (R := R) B hB ⟶ X))
    (hxy : ∀ i, pfFrom A B hB ≫ y i = x) : pfOb (R := R) (K n) (hK n) ⟶ X :=
  ObjectProperty.homMk (CommAlgCat.ofHom
    { toRingHom := Classical.choose ((hι n).ex X.obj x.hom.hom.toRingHom (fun i => (y i).hom.hom.toRingHom)
        (fun i => RingHom.ext fun c => congrArg (fun φ => φ.hom.hom c) (hxy i)))
      commutes' := fun c => by
        have h := (Classical.choose_spec ((hι n).ex X.obj x.hom.hom.toRingHom (fun i => (y i).hom.hom.toRingHom)
          (fun i => RingHom.ext fun c => congrArg (fun φ => φ.hom.hom c) (hxy i)))).1
        rw [IsScalarTower.algebraMap_apply R A.obj (K n)]
        exact (RingHom.congr_fun h _).trans (x.hom.hom.commutes c) })

theorem univMap_spec (n : ℕ) (X : PfC p R) (x : A ⟶ X) (y : Fin n → (pfOb (R := R) B hB ⟶ X))
    (hxy : ∀ i, pfFrom A B hB ≫ y i = x) :
    (univMap A B hB K hK ι hι n X x y hxy).hom.hom.toRingHom.comp (algebraMap A.obj (K n)) = x.hom.hom.toRingHom ∧
      ∀ i, (univMap A B hB K hK ι hι n X x y hxy).hom.hom.toRingHom.comp (ι n i : B →+* K n) = (y i).hom.hom.toRingHom :=
  Classical.choose_spec ((hι n).ex X.obj x.hom.hom.toRingHom (fun i => (y i).hom.hom.toRingHom)
    (fun i => RingHom.ext fun c => congrArg (fun φ => φ.hom.hom c) (hxy i)))

def mkPowers : Powers j A where
  B := pfOb (R := R) B hB
  f := pfFrom A B hB
  K n := pfOb (R := R) (K n) (hK n)
  a n := pfFrom A (K n) (hK n)
  ι n i := pfHom ((ι n i).restrictScalars R)
  w n i := pf_ext fun c => (ι n i).commutes c
  δ n k := pfHom ((δ n k).restrictScalars R)
  aδ n k := pf_ext fun c => (δ n k).commutes c
  ιδ n k i := pf_ext fun c => AlgHom.congr_fun (hδ n k i) c
  rel n k i := pf_ext fun c => AlgHom.congr_fun (hrel n k i) c
  iso0 := by
    rw [← ObjectProperty.isIso_hom_iff]
    exact (CommAlgCat.isoMk (AlgEquiv.ofBijective (IsScalarTower.toAlgHom R A.obj (K 0)) h0)).isIso_hom
  iso1 := by
    rw [← ObjectProperty.isIso_hom_iff]
    exact (CommAlgCat.isoMk (AlgEquiv.ofBijective ((ι 1 0).restrictScalars R) h1)).isIso_hom
  univ n t x y hxy := by
    refine ⟨univMap A B hB K hK ι hι n (j.obj t) x y hxy, ⟨?_, fun i => ?_⟩, fun z hz => ?_⟩
    · exact pf_ext fun c => RingHom.congr_fun (univMap_spec A B hB K hK ι hι n (j.obj t) x y hxy).1 c
    · exact pf_ext fun c => RingHom.congr_fun ((univMap_spec A B hB K hK ι hι n (j.obj t) x y hxy).2 i) c
    · have hs := univMap_spec A B hB K hK ι hι n (j.obj t) x y hxy
      exact pf_ext fun c => RingHom.congr_fun ((hι n).uniq (j.obj t).obj z.hom.hom.toRingHom
        (univMap A B hB K hK ι hι n (j.obj t) x y hxy).hom.hom.toRingHom
        (RingHom.ext fun c => (congrArg (fun φ => φ.hom.hom c) hz.1).trans (RingHom.congr_fun hs.1 c).symm)
        (fun i => RingHom.ext fun c => (congrArg (fun φ => φ.hom.hom c) (hz.2 i)).trans
          (RingHom.congr_fun (hs.2 i) c).symm)) c

theorem mkPowers_dK (N : Type) [AddCommGroup N] [Module R N] (n : ℕ) (w : N ⊗[R] K n) :
    (mkPowers j A B hB K hK ι hι δ hδ hrel h0 h1).dK j (tensF p R N) n w = ((alt (δ n)).restrictScalars R).lTensor N w := by
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add u v hu hv => rw [map_add (f := _), map_add (f := _), hu, hv]
  | tmul a b =>
    rw [Powers.dK, LinearMap.lTensor_tmul, LinearMap.restrictScalars_apply, alt, LinearMap.sum_apply,
      LinearMap.sum_apply, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearMap.smul_apply, LinearMap.smul_apply]
    exact (map_zsmul (TensorProduct.mk R N (K (n + 1)) a) _ _).symm

end Abs

theorem powers_abs {R : Type} [CommRing R] [IsDomain R] [ValuationRing R] (p : ℕ) [Fact p.Prime]
    {T : Type u'} [Category.{v'} T] (j : T ⥤ PfC p R)
    (r : ℕ → R) (hr : IsRt p r) (hdiv : ∀ a : R, a ≠ 0 → ∃ M : ℕ, a ∣ r 0 ^ M)
    (N : Type) [AddCommGroup N] [Module R N]
    (A : PfC p R) (B : Type) [CommRing B] [Algebra R B] [Algebra A.obj B] [IsScalarTower R A.obj B] (hB : Pf p B)
    (hC : Cov p (fun k => algebraMap R A.obj (r k)) B)
    (H1 : ∀ (t : T) (x : A ⟶ j.obj t), ∃ y : pfOb (R := R) B hB ⟶ j.obj t, pfFrom A B hB ≫ y = x)
    (H3 : ∃ (t₀ : T) (g : pfOb (R := R) B hB ⟶ j.obj t₀),
      (∀ (t : T) (y : pfOb (R := R) B hB ⟶ j.obj t), ∃! φ : t₀ ⟶ t, g ≫ j.map φ = y) ∧
      Almost (Ideal.span (Set.range r)) ((tensF p R N).map g).hom) :
    ∃ P : Powers j A, P.Good j (tensF p R N) (Ideal.span (Set.range r)) := by
  choose K iK aK ι hι using fun n => Leaf.wp_ex A.obj B n
  let _ : ∀ n, Algebra R (K n) := fun n => ((algebraMap A.obj (K n)).comp (algebraMap R A.obj)).toAlgebra
  have _ : ∀ n, IsScalarTower R A.obj (K n) := fun n => IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨h0, h1, δ, hδ⟩ := Leaf.wp_cof A.obj B K ι hι
  have hrel := Leaf.wp_rel A.obj B K ι δ hι hδ
  have hK : ∀ n, Pf p (K n) := fun n => Leaf.wp_pf p A.obj B (K n) n (ι n) (hι n) A.property hB
  obtain ⟨hc1, hc2⟩ := Leaf.cech_tens p R r N A.obj B K ι δ hr hdiv A.property hB hC hι hδ
  refine ⟨mkPowers j A B hB K hK ι hι δ hδ hrel h0 h1, H1, fun s hs => ⟨?_, fun n => ?_⟩, H3⟩
  · refine injUpTo_span _ _ (fun s' hs' => ?_) s hs
    obtain ⟨k, rfl⟩ := hs'
    intro w hw
    rw [mkPowers_dK] at hw
    exact hc1 w hw k
  · refine exactUpTo_span _ _ _ (fun s' hs' => ?_) s hs
    obtain ⟨k, rfl⟩ := hs'
    intro w hw
    rw [mkPowers_dK] at hw
    obtain ⟨x, hx⟩ := hc2 n w hw k
    exact ⟨x, (mkPowers_dK j A B hB K hK ι hι δ hδ hrel h0 h1 N n x).trans hx⟩

end CrystallineSemistableComparison.D
end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TensorProduct GroundTheory.PAdicHodge CrystallineSemistableComparison.CH

universe w v u v' u' v'' u''

namespace CrystallineSemistableComparison.D

variable (l : ℕ) [Fact l.Prime]

theorem powers_good (h : ObFacts l) (N : Type) [AddCommGroup N] [Module (Ob l) N] (M : ℕ) (hN : ∀ x : N, pFlat l ^ M • x = 0)
    (A : PfC l (Ob l)) : ∃ P : Powers (testι l ⋙ toPf l) A,
      P.Good (testι l ⋙ toPf l) (tensF l (Ob l) N) (Ideal.span (Set.range (rt l))) := by
  obtain ⟨_, _, hdiv, -⟩ := h
  obtain ⟨hr, hr0⟩ := isRt_rt l
  have hrA : IsRt l (fun k => algebraMap (Ob l) A.obj (rt l k)) := fun k => by
    simp only [← map_pow, hr k]
  obtain ⟨B, _, _, hB, hC, hAIC, hVAL, hS⟩ := Leaf.cov_tower l A.obj _ A.property hrA
  let _ : Algebra (Ob l) B := ((algebraMap A.obj B).comp (algebraMap (Ob l) A.obj)).toAlgebra
  have _ : IsScalarTower (Ob l) A.obj B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact powers_abs l (testι l ⋙ toPf l) (rt l) hr
    (fun a ha => by obtain ⟨M, hM⟩ := hdiv a ha; exact ⟨M, hr0 ▸ hM⟩) N A B hB hC
    (split_clause l A B hB hS) (test_clause l N M hN B hB hAIC hVAL)

end CrystallineSemistableComparison.D
end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TensorProduct GroundTheory.PAdicHodge CrystallineSemistableComparison.CH

universe w v u v' u' v'' u''

namespace CrystallineSemistableComparison.D

variable (l : ℕ) [Fact l.Prime]

theorem rt_pow (k N : ℕ) : rt l (k + N) ^ (l ^ N) = rt l k := by
  induction N with
  | zero => rw [pow_zero, pow_one, add_zero]
  | succ N ih => rw [pow_succ', pow_mul, ← add_assoc, (isRt_rt l).1 (k + N), ih]

theorem rt_ideal (N : ℕ) : Ideal.span (Set.range (rt l)) ≤
    Ideal.span ((fun a => a ^ N) '' (Ideal.span (Set.range (rt l)) : Set (Ob l))) := by
  rw [Ideal.span_le]
  rintro _ ⟨k, rfl⟩
  have hN : N ≤ l ^ N := (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le
  rw [← rt_pow l k N, ← Nat.sub_add_cancel hN, pow_add]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨rt l (k + N), Ideal.subset_span ⟨k + N, rfl⟩, rfl⟩)

theorem des_tens (h : ObFacts l) (N : Type) [AddCommGroup N] [Module (Ob l) N] (M : ℕ) (hN : ∀ x : N, pFlat l ^ M • x = 0) (k : ℕ) :
    Des (toPf l ⋙ tensF l (Ob l) N) (rt l k) := by
  have := (toPf_full l).1
  have := (toPf_full l).2
  have hdes : DesJ (testι l ⋙ toPf l) (tensF l (Ob l) N) (rt l k) := fun A =>
    CrystallineSemistableComparison.P.induct (testι l ⋙ toPf l) (tensF l (Ob l) N) _ (rt_ideal l) (fun A => powers_good l h N M hN A) A _
      (Ideal.subset_span ⟨k, rfl⟩)
  exact des_ff (testι l) (toPf l) _ _ hdes

end CrystallineSemistableComparison.D
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.FlagDomainConjHostXiEqNeg
section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.MulQExact
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CrystallineSemistableComparison.D

section SlopeTestRemainingChoices

variable {U : Type} [CommRing U]

def mulQ (a : U) (n : ℕ) : U ⧸ Ideal.span {a ^ 1} →ₗ[U] U ⧸ Ideal.span {a ^ (n + 1)} :=
  Submodule.liftQ _ ((Ideal.span {a ^ (n + 1)}).mkQ ∘ₗ LinearMap.mulLeft U (a ^ n)) (by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker]
    change Ideal.Quotient.mk _ (a ^ n * a ^ 1) = 0
    rw [pow_one, ← pow_succ]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _))

theorem mulQ_mk (a : U) (n : ℕ) (x : U) :
    mulQ a n (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (a ^ n * x) := rfl

theorem mulQ_inj (a : U) (ha : a ∈ nonZeroDivisors U) (n : ℕ) : Function.Injective (mulQ a n) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [mulQ_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hx
  obtain ⟨c, hc⟩ := hx
  refine Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton'.2 ⟨c, ?_⟩)
  have hn := pow_mem ha n
  rw [pow_succ, mul_comm (a ^ n) a, ← mul_assoc, mul_comm _ (a ^ n)] at hc
  rw [pow_one]
  exact (mul_cancel_left_mem_nonZeroDivisors hn).1 hc

theorem mulQ_exact (a : U) (n : ℕ) :
    Function.Exact (mulQ a n) (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow a n.le_succ))) := by
  intro x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨Ideal.Quotient.mk _ c, by rw [mulQ_mk, mul_comm]⟩
  · rintro ⟨z, hz⟩
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [mulQ_mk, Ideal.Quotient.eq, Ideal.mem_span_singleton'] at hz
    obtain ⟨d, hd⟩ := hz
    exact ⟨c - d * a, by rw [sub_mul, mul_assoc, ← pow_succ', hd]; ring⟩

end SlopeTestRemainingChoices

end CrystallineSemistableComparison.D
end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TensorProduct GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.D

open PAlg

variable {l : ℕ} [Fact l.Prime]

theorem flagDomainConj_hostXi_eq_neg : WittVector.constantCoeff (xi0 l) = -pFlat l := by
  rw [xi0, map_sub, map_natCast, CharP.cast_eq_zero, zero_sub]
  exact congrArg Neg.neg (WittVector.teichmuller_coeff_zero l _)

theorem un_rep {A : PAlg l} {n : ℕ} (x : A.Un n) : ∃ w : A.W, x = Ideal.Quotient.mk _ (A.th w) := by
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {A.xi}) u
  exact ⟨w, rfl⟩

variable (A : PAlg l)

def rho0 : A.U →+* A.A ⧸ Ideal.span {A.pi} :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp WittVector.constantCoeff) fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    have e : WittVector.constantCoeff A.xi = -A.pi := by
      change (WittVector.map A.s (xi0 l)).coeff 0 = -A.s (pFlat l)
      rw [WittVector.map_coeff, ← map_neg, ← flagDomainConj_hostXi_eq_neg]; rfl
    rw [RingHom.comp_apply, map_mul, e]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_left _ _ (neg_mem (Ideal.mem_span_singleton_self _)))

def rho : A.Un 1 →+* A.A ⧸ Ideal.span {A.pi} :=
  Ideal.Quotient.lift _ (rho0 A) fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, map_pow, map_natCast, ← map_natCast (Ideal.Quotient.mk (Ideal.span {A.pi})), A.natCast_l, map_zero,
      zero_pow one_ne_zero, mul_zero]

theorem rho_mk (w : A.W) : rho A (Ideal.Quotient.mk _ (A.th w)) = Ideal.Quotient.mk _ (w.coeff 0) := rfl

theorem rho_bij (hU : RU l) : Function.Bijective (rho A) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun y => ?_⟩
  · obtain ⟨w, rfl⟩ := un_rep x
    rw [rho_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
    have := ((hU A).2 w).2 hx
    exact Ideal.Quotient.eq_zero_iff_mem.2 (by rwa [pow_one])
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk _ (A.th (WittVector.teichmuller l a)), by rw [rho_mk, WittVector.teichmuller_coeff_zero]⟩

theorem span_pi_eq : (Ideal.span {A.pi}).restrictScalars (Ob l) = (Ideal.span {pFlat l} • ⊤ : Submodule (Ob l) A.A) := by
  rw [Submodule.ideal_span_singleton_smul]
  ext x
  rw [Submodule.restrictScalars_mem, Ideal.mem_span_singleton', Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, trivial, by rw [Algebra.smul_def, mul_comm]; rfl⟩
  · rintro ⟨b, _, rfl⟩
    exact ⟨b, by rw [Algebra.smul_def, mul_comm]; rfl⟩

def kappa : (A.A ⧸ Ideal.span {A.pi}) ≃ₗ[Ob l] A.A ⧸ (Ideal.span {pFlat l} • ⊤ : Submodule (Ob l) A.A) :=
  (Submodule.Quotient.restrictScalarsEquiv (Ob l) (Ideal.span {A.pi})).symm.trans (Submodule.quotEquivOfEq _ _ (span_pi_eq A))

def tau1 : A.Un 1 →+ (Ob l ⧸ Ideal.span {pFlat l}) ⊗[Ob l] A.A :=
  ((TensorProduct.quotTensorEquivQuotSMul A.A (Ideal.span {pFlat l})).symm.toAddMonoidHom.comp
    (kappa A).toAddMonoidHom).comp (rho A).toAddMonoidHom

theorem kappa_mk (x : A.A) :
    kappa A (Ideal.Quotient.mk _ x) = Submodule.Quotient.mk (p := (Ideal.span {pFlat l} • ⊤ : Submodule (Ob l) A.A)) x := by
  rfl

theorem tau1_mk (w : A.W) : tau1 A (Ideal.Quotient.mk _ (A.th w)) = (1 : Ob l ⧸ Ideal.span {pFlat l}) ⊗ₜ[Ob l] w.coeff 0 := by
  change (TensorProduct.quotTensorEquivQuotSMul A.A (Ideal.span {pFlat l})).symm (kappa A (rho A (Ideal.Quotient.mk _ (A.th w)))) = _
  rw [rho_mk, kappa_mk]
  exact TensorProduct.quotTensorEquivQuotSMul_symm_mk _ _

theorem tau1_bijective (hU : RU l) : Function.Bijective (tau1 A) :=
  (TensorProduct.quotTensorEquivQuotSMul A.A (Ideal.span {pFlat l})).symm.bijective.comp
    ((kappa A).bijective.comp (rho_bij A hU))

theorem tau1_smul (a : Ainf l) (x : A.Un 1) :
    tau1 A (a • x) = WittVector.constantCoeff a • tau1 A x := by
  obtain ⟨w, rfl⟩ := un_rep x
  have e : a • (Ideal.Quotient.mk (Ideal.span {(l : A.U) ^ 1}) (A.th w)) =
      Ideal.Quotient.mk (Ideal.span {(l : A.U) ^ 1}) (A.th (A.sW a * w)) := by
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply (Ainf l) A.U, Ideal.Quotient.algebraMap_eq, ← map_mul, map_mul A.th]; rfl
  rw [e, tau1_mk, tau1_mk, ← TensorProduct.tmul_smul, WittVector.mul_coeff_zero, Algebra.smul_def]
  change _ ⊗ₜ[Ob l] ((WittVector.map A.s a).coeff 0 * _) = _
  rw [WittVector.map_coeff]; rfl

end CrystallineSemistableComparison.D
end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TensorProduct GroundTheory.PAdicHodge CrystallineSemistableComparison.CH

universe w v u v' u' v'' u''

namespace CrystallineSemistableComparison.D

variable (l : ℕ) [Fact l.Prime]

theorem rtW_dvd (k : ℕ) : rtW l (k + 2) ^ 3 ∣ rtW l k ∧ (rtW l k).coeff 0 = rt l k := by
  refine ⟨?_, WittVector.teichmuller_coeff_zero l _⟩
  have h := (isRt_rt l).1
  have e : rt l k = rt l (k + 2) ^ (l * l) := by rw [pow_mul, h (k + 1), h k]
  have h2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hl : 3 ≤ l * l := by nlinarith
  refine ⟨WittVector.teichmuller l (rt l (k + 2) ^ (l * l - 3)), ?_⟩
  rw [rtW, rtW, e, ← map_pow, ← map_mul, ← pow_add, Nat.add_sub_cancel' hl]

theorem des_Un_one (h : ObFacts l) (hU : RU l) (k : ℕ) : Des (UnF l 1) (rtW l k) := by
  have hd := des_tens l h (Ob l ⧸ Ideal.span {pFlat l}) 1 (fun x => by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk _ (pFlat l ^ 1 * y) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_right _ _ (by rw [pow_one]; exact Ideal.mem_span_singleton_self _))) k
  have hn : ∀ {A B : PAlg l} (f : A ⟶ B) (x : (UnF l 1).obj A),
      tau1 B (((UnF l 1).map f).hom x) = ((toPf l ⋙ tensF l (Ob l) (Ob l ⧸ Ideal.span {pFlat l})).map f).hom (tau1 A x) := by
    intro A B f x
    obtain ⟨w, rfl⟩ := un_rep x
    have e : ((UnF l 1).map f).hom (Ideal.Quotient.mk _ (A.th w)) = Ideal.Quotient.mk _ (B.th (PAlg.mapW f w)) := rfl
    rw [e, tau1_mk, tau1_mk, PAlg.mapW, WittVector.map_coeff]
    rfl
  refine (des_semi WittVector.constantCoeff (testι l) (UnF l 1) (toPf l ⋙ tensF l (Ob l) (Ob l ⧸ Ideal.span {pFlat l}))
    (fun A => tau1 A) (fun A a x => tau1_smul A a x) (fun A => tau1_bijective A hU) hn (rtW l k)).2 ?_
  change DesJ _ _ ((rtW l k).coeff 0)
  rw [(rtW_dvd l k).2]
  exact hd

theorem des_Un (h : ObFacts l) (hU : RU l) (n k : ℕ) : Des (UnF l n) (rtW l k) := by
  induction n generalizing k with
  | zero =>
    refine des_span (testι l) (UnF l 0) {rtW l k} (fun a _ => Or.inr fun A x => ?_) _ (Ideal.subset_span rfl)
    have hz : ∀ z : A.Un 0, z = 0 := fun z => by
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact Ideal.Quotient.eq_zero_iff_mem.2 (by rw [pow_zero, Ideal.span_singleton_one]; trivial)
    exact hz _
  | succ n ih =>
    have hα : ∀ (A : PAlg l) (a : Ainf l) (x : (UnF l 1).obj A),
        (mulQ (l : A.U) n).toAddMonoidHom (RingHom.id (Ainf l) a • x) = RingHom.id (Ainf l) a • (mulQ (l : A.U) n).toAddMonoidHom x := by
      intro A a x
      obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
      change mulQ (l : A.U) n (a • Ideal.Quotient.mk _ u) = a • mulQ (l : A.U) n (Ideal.Quotient.mk _ u)
      rw [algebra_compatible_smul A.U a, LinearMap.map_smul, ← algebra_compatible_smul]
    have hβ : ∀ (A : PAlg l) (a : Ainf l) (x : (UnF l (n + 1)).obj A),
        (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow (l : A.U) n.le_succ))).toAddMonoidHom
          (RingHom.id (Ainf l) a • x) = RingHom.id (Ainf l) a •
        (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow (l : A.U) n.le_succ))).toAddMonoidHom x := by
      intro A a x
      obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl
    have nα : ∀ {A B : PAlg l} (f : A ⟶ B) (x : (UnF l 1).obj A),
        (mulQ (l : B.U) n).toAddMonoidHom (((UnF l 1).map f).hom x) = ((UnF l (n + 1)).map f).hom ((mulQ (l : A.U) n).toAddMonoidHom x) := by
      intro A B f x
      obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
      change Ideal.Quotient.mk _ ((l : B.U) ^ n * PAlg.mapU f u) = Ideal.Quotient.mk _ (PAlg.mapU f ((l : A.U) ^ n * u))
      rw [map_mul (PAlg.mapU f), map_pow (PAlg.mapU f), map_natCast (PAlg.mapU f)]
    have nβ : ∀ {A B : PAlg l} (f : A ⟶ B) (x : (UnF l (n + 1)).obj A),
        (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow (l : B.U) n.le_succ))).toAddMonoidHom
          (((UnF l (n + 1)).map f).hom x) = ((UnF l n).map f).hom
        ((Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow (l : A.U) n.le_succ))).toAddMonoidHom x) := by
      intro A B f x
      obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl
    have key := (des_ses (RingHom.id (Ainf l)) (RingHom.id _) (RingHom.id _) (testι l) (UnF l 1) (UnF l (n + 1)) (UnF l n)
      (fun A => (mulQ (l : A.U) n).toAddMonoidHom)
      (fun A => (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow (l : A.U) n.le_succ))).toAddMonoidHom)
      hα hβ nα nβ (fun A => mulQ_inj _ (hU A).1 n) (fun A => mulQ_exact _ n)
      (fun A y => by
        obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
        exact ⟨Ideal.Quotient.mk _ z, rfl⟩) (rtW l (k + 2))).1
      (des_Un_one l h hU (k + 2)) (ih (k + 2))
    exact des_span (testι l) (UnF l (n + 1)) {rtW l (k + 2) ^ 3}
      (fun a ha => Or.inl (by rw [Set.mem_singleton_iff.1 ha]; exact key)) _ (Ideal.mem_span_singleton.2 (rtW_dvd l k).1)

theorem wm_span (h : ObFacts l) (s : Ainf l) (hs : InWm l s) (n : ℕ) :
    s ∈ Ideal.span (insert ((l : Ainf l) ^ n) (Set.range (rtW l))) := by
  obtain ⟨_, _, _, h4⟩ := h
  have hr : ∀ k, rtW l k ∈ Ideal.span (insert ((l : Ainf l) ^ n) (Set.range (rtW l))) :=
    fun k => Ideal.subset_span (Set.mem_insert_of_mem _ ⟨k, rfl⟩)
  have hl : (l : Ainf l) ^ n ∈ Ideal.span (insert ((l : Ainf l) ^ n) (Set.range (rtW l))) :=
    Ideal.subset_span (Set.mem_insert _ _)
  cases n with
  | zero =>
    rw [Ideal.eq_top_of_isUnit_mem _ hl (by rw [pow_zero]; exact isUnit_one)]
    exact Submodule.mem_top
  | succ m =>
    obtain ⟨c, hc⟩ := WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff s m
    rw [sub_eq_iff_eq_add] at hc
    rw [hc]
    refine add_mem (Ideal.mul_mem_right _ _ hl) (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ ?_)
    have hnu : ¬ IsUnit (((frobeniusEquiv (Ob l) l).symm ^ i) (s.coeff i)) := fun hu =>
      hs i ((isUnit_map_iff ((frobeniusEquiv (Ob l) l).symm ^ i) _).1 hu)
    obtain ⟨k, d, hd⟩ := h4 _ hnu
    rw [hd, map_mul]
    exact Ideal.mul_mem_right _ _ (hr k)

end CrystallineSemistableComparison.D
