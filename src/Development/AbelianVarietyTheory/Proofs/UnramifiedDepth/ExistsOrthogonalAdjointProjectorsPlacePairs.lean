module

public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsNotMemForallMem
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsTorusExtensionPointsPullbackFieldPoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsOrthogonalAdjointProjectorsPlacePairs
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsOrthogonalAdjointProjectorsPlacePairs
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.PlaceProj

theorem exists_lim_pair {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
    (Y : FBChart C V O dd) {d : ℕ} [NeZero d] {I : Fin 2 → Type} [∀ g, Fintype (I g)] (p : PairData Y d I)
    (ρ : O →+* Matrix (Fin dd) (Fin dd) C) (hρ : ∀ a v, linAct (Y.B.A.act a) v = (ρ a).mulVec v) :
    ∃ M : Fin 2 → Matrix (Fin dd) (Fin dd) C, IsEnd (Y.raw p) V (M 0) (M 1) ∧ IsEnd (Y.raw p) V (M 1) (M 0) ∧
      ∀ g, ∃ (ε : O) (a : ℕ → O), IsLim V ρ a (M g) ∧ (∃ y, ε * ε - ε = (V.l : O) * y) ∧
        (∀ t, V.MM (p.em g t ε - 1)) ∧ (∀ x : O, (∀ t, V.MM (p.em g t x)) → ∃ y, ε * x = (V.l : O) * y) ∧
        (∀ m, ∃ y, a m * a m - a m = (V.l : O) ^ m * y) ∧ ∀ m, ∃ y, a m - ε = (V.l : O) * y := by
  obtain ⟨ε, hε, hε1, hεP⟩ := p.em_unr 0
  obtain ⟨a, h1, h2, h3⟩ := exists_idem_seq (V.l : O) ε hε
  obtain ⟨M, M', e1, e2, l1, l2⟩ := GlobalTheory.ActionLimit.exists_isEnd_of_limit C V O dd Y d I p a h1
  simp only [hρ] at l1 l2
  refine ⟨![M, M'], e1, e2, Fin.forall_fin_two.2 ⟨⟨ε, a, l1, hε, hε1, hεP, h2, h3⟩,
    star ε, fun m => star (a m), l2, ?_, fun t => ?_, fun x hx => ?_, fun m => ?_, fun m => ?_⟩⟩
  · obtain ⟨y, hy⟩ := hε
    exact ⟨star y, by simpa [mul_comm] using congrArg star hy⟩
  · rw [p.em_conj, star_star]; exact hε1 t
  · obtain ⟨y, hy⟩ := hεP (star x) fun t => by rw [← p.em_conj]; exact hx t
    exact ⟨star y, by simpa [mul_comm] using congrArg star hy⟩
  · obtain ⟨y, hy⟩ := h2 m
    exact ⟨star y, by simpa [mul_comm] using congrArg star hy⟩
  · obtain ⟨y, hy⟩ := h3 m
    exact ⟨star y, by simpa [mul_comm] using congrArg star hy⟩

theorem exists_orth_proj : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (Orb : Type) (I : Orb → Fin 2 → Type) [∀ o g, Fintype (I o g)] (p : ∀ o, PairData Y d (I o)), (∀ x x' : Orb × Fin 2 × ZMod d, x ≠ x' → ∃ a : O, V.v ((p x.1).em x.2.1 x.2.2 a - (p x'.1).em x'.2.1 x'.2.2 a) = 0) → ∃ M : Orb → Fin 2 → Matrix (Fin dd) (Fin dd) C, (∀ o, IsEnd (Y.raw (p o)) V (M o 0) (M o 1) ∧ IsEnd (Y.raw (p o)) V (M o 1) (M o 0)) ∧ (∀ o g c, (M o g).mulVec ((p o).u g c) = (p o).u g c) ∧ (∀ o g o' g' c, (o, g) ≠ (o', g') → (M o g).mulVec ((p o').u g' c) = 0) ∧ ∀ o g v, ∃ b : I o g → C, (M o g).mulVec v = ∑ c, b c • (p o).u g c := by
  intro C _ _ V O _ _ dd Y d _ Orb I _ p hsep
  haveI := Y.algClosed
  have hex : ∃ ρ : O →+* Matrix (Fin dd) (Fin dd) C,
      (∀ a i j, ρ a i j = MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (Y.B.A.act a i)) ∧
      ∀ a v, linAct (Y.B.A.act a) v = (ρ a).mulVec v := by
    let A := Y.B.A
    let f : O → Matrix (Fin dd) (Fin dd) C := fun a =>
      Matrix.of fun i j => MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (A.act a i)
    have law_coeff (G : Germ.FGLaw C dd) (i j : Fin dd) (k : Fin 2) :
        MvPowerSeries.coeff (Finsupp.single (k, j) 1) (G.F i) = if j = i then 1 else 0 := by
      have hX : ∀ (p q : Fin 1 × Fin dd), MvPowerSeries.coeff (Finsupp.single p 1)
          (MvPowerSeries.X q : MvPowerSeries (Fin 1 × Fin dd) C) = if p = q then 1 else 0 := by
        intro p q
        rw [MvPowerSeries.coeff_X]
        by_cases h : p = q
        · simp [h]
        · rw [if_neg, if_neg h]
          intro h'
          exact h (Finsupp.single_left_injective one_ne_zero h')
      have hX2 : ∀ (p q : Fin 2 × Fin dd), MvPowerSeries.coeff (Finsupp.single p 1)
          (MvPowerSeries.X q : MvPowerSeries (Fin 2 × Fin dd) C) = if p = q then 1 else 0 := by
        intro p q
        rw [MvPowerSeries.coeff_X]
        by_cases h : p = q
        · simp [h]
        · rw [if_neg, if_neg h]
          intro h'
          exact h (Finsupp.single_left_injective one_ne_zero h')

      have h1 : MvPowerSeries.coeff (Finsupp.single ((1 : Fin 2), j) 1) (G.F i) = if j = i then 1 else 0 := by
        have h := congrArg (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1)) (G.unit i)
        unfold Germ.ev at h
        rw [GlobalTheory.FormalCalc.coeff_single_subst (by
          rintro ⟨k, l⟩; fin_cases k <;> simp [Germ.pt])] at h
        rw [hX] at h
        simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          Pi.zero_apply, map_zero, mul_zero, Finset.sum_const_zero, zero_add, Germ.pt, hX,
          Prod.mk.injEq, true_and, mul_ite, _root_.mul_one] at h
        simpa [Finset.sum_ite_eq, Finset.sum_ite_eq', eq_comm] using h
      have h0 : MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), j) 1) (G.F i) = if j = i then 1 else 0 := by

        have h := congrArg (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), j) 1)) (G.comm i)
        unfold Germ.ev at h
        rw [GlobalTheory.FormalCalc.coeff_single_subst (by
          rintro ⟨k, l⟩; fin_cases k <;> simp [Germ.pt])] at h
        simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          Germ.pt, hX2, Prod.mk.injEq, mul_ite, _root_.mul_one, mul_zero] at h
        rw [← h1, ← h]
        simp [Finset.sum_ite_eq]
      fin_cases k
      · exact h0
      · exact h1
    have hadd : ∀ a b, f (a + b) = f a + f b := by
      intro a b
      ext i j
      simp only [f, Matrix.of_apply, Matrix.add_apply, A.add_act, FGLaw.add, addOf, ev]
      rw [GlobalTheory.FormalCalc.coeff_single_subst (by rintro ⟨k, l⟩; fin_cases k <;> simp [A.const])]
      simp [Fintype.sum_prod_type, Fin.sum_univ_two, law_coeff]
    have hmul : ∀ a b, f (a * b) = f a * f b := by
      intro a b
      ext i j
      simp only [f, Matrix.of_apply, Matrix.mul_apply, A.mul_act, comp1, ev]
      rw [GlobalTheory.FormalCalc.coeff_single_subst (by rintro ⟨k, l⟩; fin_cases k; simp [A.const])]
      simp [Fintype.sum_prod_type]
    have hone : f 1 = 1 := by
      ext i j
      simp only [f, Matrix.of_apply, A.one_act, pt, MvPowerSeries.coeff_X, Matrix.one_apply]
      simp [Finsupp.single_left_inj, eq_comm]
    exact ⟨RingHom.mk' ⟨⟨f, hone⟩, hmul⟩ hadd, fun _ _ _ => rfl, fun _ _ => rfl⟩
  obtain ⟨ρ, hρ1, hρ⟩ := hex
  have hint : ∀ x i j, V.Ge 0 (ρ x i j) := fun x i j => by rw [hρ1]; exact Y.intAct x i _
  choose M e1 e2 hM using fun o => exists_lim_pair Y (p o) ρ hρ
  have hs : ∀ o g (a a' : ZMod d), a ≠ a' → ∃ x, V.v ((p o).em g a x - (p o).em g a' x) = 0 :=
    fun o g a a' h => (p o).em_sep (g, a) (g, a') fun h' => h (congrArg Prod.snd h')
  refine ⟨M, fun o => ⟨e1 o, e2 o⟩, fun o g c => ?_, fun o g o' g' c hne => ?_, fun o g v => ?_⟩
  · obtain ⟨ε, a, hl, -, hε1, -, ha, ha0⟩ := hM o g
    have := hl.eig ((p o).em g ((p o).ty g c)) 1 (seq_one ha ha0 _ ((p o).em_int g _) (hε1 _)) ((p o).u g c)
      (fun x => by rw [← hρ, (p o).u_eig])
    rwa [one_smul] at this
  · obtain ⟨ε, a, hl, hε, hε1, hεP, ha, ha0⟩ := hM o g
    have hmm : V.MM ((p o').em g' ((p o').ty g' c) ε) := by
      by_contra hmm
      obtain ⟨t, ht⟩ := eq_em_of_not_mm ((p o).em g) ((p o).em_int g) ((p o).em_frob g) (hs o g) ε hε hε1 hεP _
        ((p o').em_int g' _) hmm
      obtain ⟨x, hx⟩ := hsep (o, g, t) (o', g', (p o').ty g' c) fun h =>
        hne (congrArg (fun z : Orb × Fin 2 × ZMod d => (z.1, z.2.1)) h)
      simp [ht] at hx
    have := hl.eig ((p o').em g' ((p o').ty g' c)) 0 (seq_zero ha ha0 _ ((p o').em_int g' _) hmm) ((p o').u g' c)
      (fun x => by rw [← hρ, (p o').u_eig])
    rwa [zero_smul] at this
  · obtain ⟨ε, a, hl, hε, hε1, hεP, ha, ha0⟩ := hM o g
    have := hl.range hint ((p o).em g) ((p o).em_int g) ((p o).em_frob g) (hs o g) ε hε hε1 hεP ha ha0
      (Submodule.span C (Set.range ((p o).u g))) (fun t w hw => by
        obtain ⟨b, -, hb⟩ := (p o).u_full g t w fun x => by rw [hρ, hw]
        exact (Submodule.mem_span_range_iff_exists_fun C).2 ⟨b, hb.symm⟩) v
    obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun C).1 this
    exact ⟨b, hb.symm⟩

end GlobalTheory.PlaceProj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsOrthogonalAdjointProjectorsPlacePairsStatement
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthogonal_adjoint_projectors_placePairs : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (Orb : Type) (I : Orb → Fin 2 → Type) [∀ o g, Fintype (I o g)] (p : ∀ o, PairData Y d (I o)), (∀ x x' : Orb × Fin 2 × ZMod d, x ≠ x' → ∃ a : O, V.v ((p x.1).em x.2.1 x.2.2 a - (p x'.1).em x'.2.1 x'.2.2 a) = 0) → ∃ M : Orb → Fin 2 → Matrix (Fin dd) (Fin dd) C, (∀ o, IsEnd (Y.raw (p o)) V (M o 0) (M o 1) ∧ IsEnd (Y.raw (p o)) V (M o 1) (M o 0)) ∧ (∀ o g c, (M o g).mulVec ((p o).u g c) = (p o).u g c) ∧ (∀ o g o' g' c, (o, g) ≠ (o', g') → (M o g).mulVec ((p o').u g' c) = 0) ∧ ∀ o g v, ∃ b : I o g → C, (M o g).mulVec v = ∑ c, b c • (p o).u g c := by
  first | exact @GlobalTheory.PlaceProj.exists_orth_proj | exact GlobalTheory.PlaceProj.exists_orth_proj | (intros; apply GlobalTheory.PlaceProj.exists_orth_proj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AlphaPHomomorphismCubicalWeilTrivialRationalTors
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AlphaPHomomorphismCubicalWeilTrivialRationalTors
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair

def unitsOfΓ {S : Scheme.{0}} {Ω : Type} [Field Ω] (s : Sp Ω ⟶ S) (A : Type) [CommRing A] [Algebra Ω A] :
    Γ((overAt s A).left, ⊤)ˣ →* Aˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.toMonoidHom

theorem unitsOfΓ_injective {S : Scheme.{0}} {Ω : Type} [Field Ω] (s : Sp Ω ⟶ S) (A : Type) [CommRing A]
    [Algebra Ω A] : Function.Injective (unitsOfΓ s A) :=
  Units.map_injective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).hom).1

theorem unitsOfΓ_natural {S : Scheme.{0}} {Ω : Type} [Field Ω] (s : Sp Ω ⟶ S) {A B : Type} [CommRing A]
    [Algebra Ω A] [CommRing B] [Algebra Ω B] (f : A →ₐ[Ω] B) (ζ : Γ((overAt s A).left, ⊤)ˣ) :
    unitsOfΓ s B (Units.map (homAt s f).left.appTop.hom.toMonoidHom ζ) = Units.map (f : A →* B) (unitsOfΓ s A ζ) := by
  have h₁ := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (f : A →+* B))
  exact Units.ext (congrArg (fun φ => φ.hom ζ.val) h₁)

theorem cubWeil_alpha_rational : ∀ (Ω : Type) [Field Ω] (p : ℕ) [Fact p.Prime] [CharP Ω p] (S : Scheme.{0}) (s : Sp Ω ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (c : CubicalStr G L) (g : Fam s G), IsAlpha p s G g → ∀ x : overAt s Ω ⟶ G, x ^ p = 1 → ∀ (A : Type) [CommRing A] [Algebra Ω A] (a : A), a ^ p = 0 → CubWeil c p (g A a) (homAt s (Algebra.ofId Ω A) ≫ x) 1 := by
  intro Ω _ p _ _ S s G _ _ L c g hg x hx
  classical
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hex : ∀ (A : Type) [CommRing A] [Algebra Ω A] (a : A), ∃ ζ : Γ((overAt s A).left, ⊤)ˣ,
      a ^ p = 0 → CubWeil c p (g A a) (homAt s (Algebra.ofId Ω A) ≫ x) ζ := by
    intro A _ _ a
    by_cases ha : a ^ p = 0
    · obtain ⟨ζ, hζ, -⟩ := UU.existsUnique_cubWeil c (hg.pow_eq_one hp ha)
        (y := homAt s (Algebra.ofId Ω A) ≫ x) (by rw [← MonObj.comp_pow, hx, MonObj.comp_one])
      exact ⟨ζ, fun _ => hζ⟩
    · exact ⟨1, fun h => absurd h ha⟩
  choose ζ hζ using hex
  intro A _ _ a ha
  have key := GlobalTheory.T.alphaP_multiplicativeCharacter_eq_one Ω p (fun A _ _ a => unitsOfΓ s A (ζ A a)) ?_ ?_ A a ha
  · have : ζ A a = 1 := unitsOfΓ_injective s A (key.trans (map_one _).symm)
    exact this ▸ hζ A a ha
  · intro A B _ _ _ _ f a ha
    beta_reduce
    have hb : f a ^ p = 0 := by rw [← map_pow, ha, map_zero]
    have h₁ := (hζ A a ha).comp (homAt s f)
    rw [← hg.1 A B f a ha, ← Category.assoc, hom_comp, Subsingleton.elim (f.comp (Algebra.ofId Ω A)) (Algebra.ofId Ω B)] at h₁
    rw [(hζ B (f a) hb).unique h₁, unitsOfΓ_natural]
  · intro A _ _ a a' ha ha'
    beta_reduce
    have hs : (a + a') ^ p = 0 := by
      rcases subsingleton_or_nontrivial A with _ | _
      · exact Subsingleton.elim _ _
      · haveI : CharP A p := charP_of_injective_algebraMap (algebraMap Ω A).injective p
        rw [add_pow_char, ha, ha', add_zero]
    have h₁ := (hζ A a ha).mul_left (hζ A a' ha')
    rw [← hg.2 A a a' ha ha'] at h₁
    rw [(hζ A (a + a') hs).unique h₁, map_mul]

end GlobalTheory.AlphaPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AlphaPHomomorphismCubicalWeilTrivialRationalTorsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alphaP_homomorphism_cubicalWeil_trivial_rational_torsion : ∀ (Ω : Type) [Field Ω] (p : ℕ) [Fact p.Prime] [CharP Ω p] (S : Scheme.{0}) (s : Sp Ω ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (c : CubicalStr G L) (g : Fam s G), IsAlpha p s G g → ∀ x : overAt s Ω ⟶ G, x ^ p = 1 → ∀ (A : Type) [CommRing A] [Algebra Ω A] (a : A), a ^ p = 0 → CubWeil c p (g A a) (homAt s (Algebra.ofId Ω A) ≫ x) 1 := by
  first | exact @GlobalTheory.AlphaPair.cubWeil_alpha_rational | exact GlobalTheory.AlphaPair.cubWeil_alpha_rational | (intros; apply GlobalTheory.AlphaPair.cubWeil_alpha_rational <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsFormalChartPointNilpotentCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsFormalChartPointNilpotentCoordinates
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair.JetPt

section Rho

variable {V Ω : Type} [CommRing V] [CommRing Ω] (β : V →+* Ω)

def Compat {B A : Type} [CommRing B] [Algebra V B] [CommRing A] [Algebra Ω A] (ψ : B →+* A) : Prop :=
  ∀ v : V, ψ (algebraMap V B v) = algebraMap Ω A (β v)

variable {β}

theorem Compat.left {B B' A : Type} [CommRing B] [Algebra V B] [CommRing B'] [Algebra V B'] [CommRing A] [Algebra Ω A]
    {ψ : B →+* A} (h : Compat β ψ) (f : B' →ₐ[V] B) : Compat β (ψ.comp (f : B' →+* B)) := fun v => by
  rw [RingHom.comp_apply, RingHom.coe_coe, f.commutes, h v]

theorem Compat.right {B A A' : Type} [CommRing B] [Algebra V B] [CommRing A] [Algebra Ω A] [CommRing A'] [Algebra Ω A']
    {ψ : B →+* A} (h : Compat β ψ) (g : A →ₐ[Ω] A') : Compat β ((g : A →+* A').comp ψ) := fun v => by
  rw [RingHom.comp_apply, h v, RingHom.coe_coe, g.commutes]

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

def rho {B A : Type} [CommRing B] [Algebra V B] [CommRing A] [Algebra Ω A] (ψ : B →+* A) (h : Compat β ψ) :
    overAt (spMap β) A ⟶ overAt (𝟙 (Sp V)) B :=
  Over.homMk (spMap ψ) (by
    change spMap ψ ≫ spMap (algebraMap V B) ≫ 𝟙 _ = spMap (algebraMap Ω A) ≫ spMap β
    rw [Category.comp_id, sp_comp, sp_comp]
    congr 1
    exact RingHom.ext h)

theorem rho_homAt {B B' A : Type} [CommRing B] [Algebra V B] [CommRing B'] [Algebra V B'] [CommRing A] [Algebra Ω A]
    {ψ : B →+* A} (h : Compat β ψ) (f : B' →ₐ[V] B) :
    rho ψ h ≫ homAt (𝟙 (Sp V)) f = rho (ψ.comp (f : B' →+* B)) (h.left f) :=
  Over.OverMorphism.ext (sp_comp _ _)

theorem homAt_rho {B A A' : Type} [CommRing B] [Algebra V B] [CommRing A] [Algebra Ω A] [CommRing A'] [Algebra Ω A']
    {ψ : B →+* A} (h : Compat β ψ) (g : A →ₐ[Ω] A') :
    homAt (spMap β) g ≫ rho ψ h = rho ((g : A →+* A').comp ψ) (h.right g) :=
  Over.OverMorphism.ext (sp_comp _ _)

def co {d m : ℕ} {A : Type} [CommRing A] (ψ : Jet V (Fin 1 × Fin d) m →+* A) : Fin d → A :=
  fun j => ψ (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j)))

theorem eq_of_co {d m : ℕ} {A : Type} [CommRing A] [Algebra Ω A] {ψ ψ' : Jet V (Fin 1 × Fin d) m →+* A}
    (h : Compat β ψ) (h' : Compat β ψ') (e : co ψ = co ψ') : ψ = ψ' := by
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun v => (h v).trans (h' v).symm) ?_)
  rintro ⟨i, j⟩
  obtain rfl : i = 0 := Subsingleton.elim _ _
  exact congrFun e j

theorem jetMap_X {κ κ' : Type} {m : ℕ} (φ : κ → MvPolynomial κ' V) (hφ : ∀ i, φ i ∈ orig V κ') (i : κ) :
    (jetMap φ hφ : Jet V κ m →ₐ[V] Jet V κ' m) (Ideal.Quotient.mk _ (MvPolynomial.X i)) =
      Ideal.Quotient.mk _ (φ i) := by
  change Ideal.Quotient.mk _ (MvPolynomial.aeval φ (MvPolynomial.X i)) = _
  rw [MvPolynomial.aeval_X]

theorem jetAug_X {κ : Type} {m : ℕ} (i : κ) :
    (jetAug : Jet V κ m →ₐ[V] V) (Ideal.Quotient.mk _ (MvPolynomial.X i)) = 0 := by
  change MvPolynomial.aeval (fun _ : κ => (0 : V)) (MvPolynomial.X i) = _
  rw [MvPolynomial.aeval_X]

theorem exists_jet {κ : Type} [Fintype κ] [DecidableEq κ] {A : Type} [CommRing A] [Algebra Ω A] (a : κ → A)
    (ha : ∀ i, IsNilpotent (a i)) :
    ∃ (m : ℕ) (ψ : Jet V κ m →+* A), Compat β ψ ∧ ∀ i, ψ (Ideal.Quotient.mk _ (MvPolynomial.X i)) = a i := by
  have hn : IsNilpotent (Ideal.span (Set.range a)) := by
    refine (Ideal.FG.isNilpotent_iff_le_nilradical (Submodule.fg_span (Set.finite_range a))).2 (Ideal.span_le.2 ?_)
    rintro _ ⟨i, rfl⟩
    exact ha i
  obtain ⟨m, hm⟩ := hn
  obtain ⟨ψ, hψ, -⟩ := (GlobalTheory.AlphaPair.JetEv.jet_hom_spec V Ω A β κ m).1 a (by rw [pow_succ, hm, zero_mul]; rfl)
  exact ⟨m, ψ, hψ⟩

theorem exists_jet_one {d : ℕ} {A : Type} [CommRing A] [Algebra Ω A] (a : Fin d → A)
    (ha : ∀ i, IsNilpotent (a i)) :
    ∃ (m : ℕ) (ψ : Jet V (Fin 1 × Fin d) m →+* A), Compat β ψ ∧ co ψ = a := by
  obtain ⟨m, ψ, h, e⟩ := exists_jet (β := β) (fun q : Fin 1 × Fin d => a q.2) fun q => ha q.2
  exact ⟨m, ψ, h, funext fun j => e (0, j)⟩

variable {G : Over (Sp V)} {d : ℕ} {x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G}

theorem lift_add (hx : ∀ m, homAt (𝟙 (Sp V))
      (jetTrunc : Jet V (Fin 1 × Fin d) (m + 1) →ₐ[V] Jet V (Fin 1 × Fin d) m) ≫ x (m + 1) = x m)
    {A : Type} [CommRing A] [Algebra Ω A] {m : ℕ} (ψ : Jet V (Fin 1 × Fin d) m →+* A) (h : Compat β ψ)
    {n : ℕ} (hn : m ≤ n) :
    ∃ (χ : Jet V (Fin 1 × Fin d) n →+* A) (hχ : Compat β χ), co χ = co ψ ∧ rho χ hχ ≫ x n = rho ψ h ≫ x m := by
  induction n, hn using Nat.le_induction with
  | base => exact ⟨ψ, h, rfl, rfl⟩
  | succ n _ ih =>
    obtain ⟨χ, hχ, e, e'⟩ := ih
    refine ⟨_, hχ.left jetTrunc, e, ?_⟩
    rw [← rho_homAt hχ, Category.assoc, hx, e']

theorem indep (hx : ∀ m, homAt (𝟙 (Sp V))
      (jetTrunc : Jet V (Fin 1 × Fin d) (m + 1) →ₐ[V] Jet V (Fin 1 × Fin d) m) ≫ x (m + 1) = x m)
    {A : Type} [CommRing A] [Algebra Ω A] {m n : ℕ} {ψ : Jet V (Fin 1 × Fin d) m →+* A} (h : Compat β ψ)
    {ψ' : Jet V (Fin 1 × Fin d) n →+* A} (h' : Compat β ψ') (e : co ψ = co ψ') :
    rho ψ h ≫ x m = rho ψ' h' ≫ x n := by
  obtain ⟨χ, hχ, e₁, e₂⟩ := lift_add hx ψ h (le_max_left m n)
  obtain ⟨χ', hχ', e₁', e₂'⟩ := lift_add hx ψ' h' (le_max_right m n)
  obtain rfl : χ = χ' := eq_of_co hχ hχ' (by rw [e₁, e₁', e])
  rw [← e₂, ← e₂']

end Rho

section Main

variable {V Ω : Type} [CommRing V] [Field Ω] (β : V →+* Ω) {G : Over (Sp V)} [GrpObj G] {d : ℕ}
  (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G)


open Classical in
def ptOf : PtFam (spMap β) G d := fun A _ _ a =>
  if h : ∃ p : (m : ℕ) × (Jet V (Fin 1 × Fin d) m →+* A), Compat β p.2 ∧ co p.2 = a then
    rho h.choose.2 h.choose_spec.1 ≫ x h.choose.1
  else 1

variable {β x}

theorem ptOf_co (hx : ∀ m, homAt (𝟙 (Sp V))
      (jetTrunc : Jet V (Fin 1 × Fin d) (m + 1) →ₐ[V] Jet V (Fin 1 × Fin d) m) ≫ x (m + 1) = x m)
    {A : Type} [CommRing A] [Algebra Ω A] {m : ℕ} {ψ : Jet V (Fin 1 × Fin d) m →+* A} (h : Compat β ψ)
    {a : Fin d → A} (e : co ψ = a) : ptOf β x A a = rho ψ h ≫ x m := by
  have hh : ∃ p : (m : ℕ) × (Jet V (Fin 1 × Fin d) m →+* A), Compat β p.2 ∧ co p.2 = a := ⟨⟨m, ψ⟩, h, e⟩
  rw [ptOf, dite_eq_left hh]
  exact indep hx _ h (hh.choose_spec.2.trans e.symm)

end Main

end GlobalTheory.AlphaPair.JetPt


open GlobalTheory.AlphaPair.JetPt in
theorem GlobalTheory.AlphaPair.exists_jetPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t : SAB H (Sp V)) (d : ℕ) (F : Fin d → PS V 2 d) (act : 𝓞 E → Fin d → PS V 1 d) (tg : Fin d → (Sp (DualNumber V) ⟶ t.G.left)) (uv : Fin d → Fin d → V) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G), IsChartG t (𝟙 (Sp V)) d F act tg uv x → (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → ∀ (Ω : Type) [Field Ω] (β : V →+* Ω), ∃ P : PtFam (spMap β) t.G d, IsJetPt β x P ∧ IsPtLaw (spMap β) t.G (fun j => MvPowerSeries.map β (F j)) P := by
  intro E _ _ _ H V _ t d F act tg uv x hc hF Ω _ β
  refine ⟨ptOf β x, fun A _ _ m ψ h => ?_, fun A B _ _ _ _ f a ha => ?_, fun A _ _ => ?_, fun A _ _ a b ha hb => ?_⟩
  · exact congrArg CommaMorphism.left (ptOf_co hc.trunc (ψ := ψ) h rfl)
  · obtain ⟨m, ψ, h, rfl⟩ := exists_jet_one (β := β) a ha
    rw [ptOf_co hc.trunc h rfl, ptOf_co hc.trunc (h.right f) (a := fun j => f (co ψ j)) rfl, ← Category.assoc, homAt_rho]
  · have h : Compat β ((algebraMap Ω A).comp β) := fun v => rfl
    rw [ptOf_co hc.trunc (h.left (jetAug : Jet V (Fin 1 × Fin d) 0 →ₐ[V] V))
      (funext fun j => by simp only [co, RingHom.comp_apply, RingHom.coe_coe, jetAug_X, map_zero, Pi.zero_apply]),
      ← rho_homAt h, Category.assoc, hc.zero, MonObj.comp_one]
  · obtain ⟨m, ψ, h, e⟩ := exists_jet (β := β) (fun q : Fin 2 × Fin d => ![a, b] q.1 q.2) (by
      rintro ⟨i, j⟩
      fin_cases i
      exacts [ha j, hb j])
    have hi : ∀ i : Fin 2, ptOf β x A (![a, b] i) = rho ψ h ≫ jptG t (𝟙 (Sp V)) d x m i := fun i => by
      rw [jptG, ← Category.assoc, rho_homAt]
      refine ptOf_co hc.trunc _ (funext fun j => ?_)
      simp only [co, RingHom.comp_apply, RingHom.coe_coe, jetCopy, jetMap_X, e]
    have h0 : ptOf β x A a = _ := hi 0
    have h1 : ptOf β x A b = _ := hi 1
    rw [h0, h1, ← MonObj.comp_mul, ← hc.law m, ← Category.assoc, rho_homAt]
    refine ptOf_co hc.trunc _ (funext fun j => ?_)
    have h3 := ((GlobalTheory.AlphaPair.JetEv.jet_hom_spec V Ω A β (Fin 2 × Fin d) m).2 ψ h).2.2 (F j)
    simp only [e] at h3
    simp only [co, RingHom.comp_apply, RingHom.coe_coe, jetSubstP, jetMap_X]
    rw [Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh.cc_psTrunc, hF, map_zero, sub_zero]
    exact h3

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsFormalChartPointNilpotentCoordinatesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_formalChart_point_nilpotent_coordinates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t : SAB H (Sp V)) (d : ℕ) (F : Fin d → PS V 2 d) (act : 𝓞 E → Fin d → PS V 1 d) (tg : Fin d → (Sp (DualNumber V) ⟶ t.G.left)) (uv : Fin d → Fin d → V) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G), IsChartG t (𝟙 (Sp V)) d F act tg uv x → (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → ∀ (Ω : Type) [Field Ω] (β : V →+* Ω), ∃ P : PtFam (spMap β) t.G d, IsJetPt β x P ∧ IsPtLaw (spMap β) t.G (fun j => MvPowerSeries.map β (F j)) P := by
  first | exact @GlobalTheory.AlphaPair.exists_jetPt | exact GlobalTheory.AlphaPair.exists_jetPt | (intros; apply GlobalTheory.AlphaPair.exists_jetPt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FramePartialLawsNilpotentCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FramePartialLawsNilpotentCoordinates
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair.Cube

section Alg

variable {V Ω A : Type} [CommRing V] [CommRing Ω] [CommRing A] [Algebra Ω A] {β : V →+* Ω} {m d : ℕ}

theorem spMap_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem cc_psIn {n n' : ℕ} (r : Fin n → Fin n') (f : PS V n d) (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPolynomial.constantCoeff (psIn d m r f) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [psIn, MvPolynomial.constantCoeff_rename, psTrunc, map_sum]
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [MvPolynomial.constantCoeff_monomial]
  split_ifs with h
  · subst h; simpa using hf
  · rfl

theorem subst_X {κ κ' : Type} (φ : κ → MvPolynomial κ' V) (i : κ) (h : MvPolynomial.constantCoeff (φ i) = 0) :
    jetSubstP m φ (Ideal.Quotient.mk _ (MvPolynomial.X i)) = Ideal.Quotient.mk _ (φ i) := by
  simp only [jetSubstP, Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.jetMap_mk, MvPolynomial.aeval_X, h, map_zero, sub_zero]

theorem map_psIn {n n' : ℕ} (ψ : Jet V (Fin n' × Fin d) m →+* A)
    (hψ : ∀ v : V, ψ (algebraMap V _ v) = algebraMap Ω A (β v)) (r : Fin n → Fin n') (f : PS V n d) :
    ψ (Ideal.Quotient.mk _ (psIn d m r f)) =
      evP (fun i j => ψ (Ideal.Quotient.mk _ (MvPolynomial.X (r i, j)))) (MvPowerSeries.map β f) := by
  let g : Jet V (Fin n × Fin d) m →ₐ[V] Jet V (Fin n' × Fin d) m :=
    jetMap (fun p => MvPolynomial.X (r p.1, p.2)) fun _ => X_mem_orig _
  have h := ((GlobalTheory.T.jetRing_hom_exists_unique_spec V Ω A β (Fin n × Fin d) m).2 (ψ.comp g) (fun v => by
    simp only [RingHom.comp_apply, RingHom.coe_coe, AlgHom.commutes, hψ])).2.2 f
  simp only [g, psJet, RingHom.comp_apply, RingHom.coe_coe, Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.jetMap_mk, MvPolynomial.aeval_X] at h
  rw [evP, ← h, psIn, MvPolynomial.rename_eq_aeval]
  rfl

theorem gm_unit {B : Type} [CommRing B] (ψ : B →+* A) (z : Sp A) (u : Bˣ) :
    (gm (spMap ψ) z ⊤ (unitΓ u)).val = gs (𝟙 (Sp A)) z ⊤ (toΓ A (ψ u)) := by
  rw [gm_val _ _ ⊤ trivial, gs_eq _ _ ⊤ trivial]
  have h := congrArg (fun q => q.hom (u : B)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ))
  exact congrArg ((Sp A).presheaf.germ ⊤ z trivial).hom h.symm

end Alg

section Frame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V] {t : SAB H (Sp V)}
  {d : ℕ} {x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G} {Ω : Type} [Field Ω] {β : V →+* Ω}
  {A : Type} [CommRing A] [Algebra Ω A] {m : ℕ}

def ptOf {n : ℕ} (ψ : Jet V (Fin n × Fin d) m →+* A) (hψ : ∀ v : V, ψ (algebraMap V _ v) = algebraMap Ω A (β v)) :
    overAt (spMap β) A ⟶ jOG (𝟙 (Sp V)) d m n :=
  Over.homMk (spMap ψ) (by
    change spMap ψ ≫ spMap _ ≫ 𝟙 _ = spMap _ ≫ spMap β
    rw [Category.comp_id, spMap_spMap, spMap_spMap]
    exact congrArg spMap (RingHom.ext hψ))

theorem ptOf_jpt {P : PtFam (spMap β) t.G d} (hP : IsJetPt β x P) {n : ℕ} (ψ : Jet V (Fin n × Fin d) m →+* A)
    (hψ : ∀ v : V, ψ (algebraMap V _ v) = algebraMap Ω A (β v)) (i : Fin n) :
    ptOf ψ hψ ≫ jptG t (𝟙 _) d x m i = P A fun j => ψ (Ideal.Quotient.mk _ (MvPolynomial.X (i, j))) := by
  have h := hP A m (ψ.comp (jetCopy d m i : Jet V (Fin 1 × Fin d) m →ₐ[V] Jet V (Fin n × Fin d) m)) (fun v => by
    simp only [RingHom.comp_apply, RingHom.coe_coe, AlgHom.commutes, hψ])
  simp only [jetCopy, RingHom.comp_apply, RingHom.coe_coe, Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.jetMap_mk, MvPolynomial.aeval_X] at h
  ext1
  rw [h, ← spMap_spMap, Category.assoc]
  rfl

theorem exists_val (β : V →+* Ω) (e : FrTyG t (𝟙 (Sp V)) d x m) (z : Sp A) (J : (Sp A ⟶ t.G.left) → t.PP.L.ι) :
    ∃ e' : (Fin d → A) → (Fin d → A) → ((Sp A).presheaf.stalk z)ˣ,
      ∀ ψ : Jet V (Fin 2 × Fin d) m →+* A, (∀ v : V, ψ (algebraMap V _ v) = algebraMap Ω A (β v)) →
        ∀ a u : Fin d → A, (∀ j, ψ (Ideal.Quotient.mk _ (MvPolynomial.X (0, j))) = a j) →
          (∀ j, ψ (Ideal.Quotient.mk _ (MvPolynomial.X (1, j))) = u j) →
          val (L := t.PP.L) (φ := cφG t ![jptG t (𝟙 _) d x m (0 : Fin 2), jptG t (𝟙 _) d x m (1 : Fin 2)])
            (ε := cε 2) e (spMap ψ) z J = e' a u := by
  classical
  let Q : (Fin d → A) → (Fin d → A) → (Jet V (Fin 2 × Fin d) m →+* A) → Prop := fun a u ψ =>
    (∀ v : V, ψ (algebraMap V _ v) = algebraMap Ω A (β v)) ∧
      ∀ q : Fin 2 × Fin d, ψ (Ideal.Quotient.mk _ (MvPolynomial.X q)) = ![a, u] q.1 q.2
  refine ⟨fun a u => if h : ∃ ψ, Q a u ψ then
    val (L := t.PP.L) (φ := cφG t ![jptG t (𝟙 _) d x m (0 : Fin 2), jptG t (𝟙 _) d x m (1 : Fin 2)])
      (ε := cε 2) e (spMap h.choose) z J else 1, fun ψ hψ a u ha hu => ?_⟩
  have hQ : Q a u ψ := ⟨hψ, by
    rintro ⟨i, j⟩
    fin_cases i
    exacts [ha j, hu j]⟩
  have h : ∃ ψ, Q a u ψ := ⟨ψ, hQ⟩
  have k : h.choose = ψ := Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext
    (fun v => (h.choose_spec.1 v).trans (hψ v).symm) fun q => (h.choose_spec.2 q).trans (hQ.2 q).symm)
  simp only [dif_pos h, k]

theorem val_pe (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) {z : Sp A} {J : (Sp A ⟶ t.G.left) → t.PP.L.ι}
    (hJ : Good t.PP.L z J) {n : ℕ} (ψ : Jet V (Fin n × Fin d) m →+* A)
    (φ : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) V) :
    val (peG t (𝟙 _) d x e m φ) (spMap ψ) z J =
      val (L := t.PP.L) (φ := cφG t ![jptG t (𝟙 _) d x m (0 : Fin 2), jptG t (𝟙 _) d x m (1 : Fin 2)])
        (ε := cε 2) (e m) (spMap (ψ.comp (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2 :
          Jet V (Fin 2 × Fin d) m →ₐ[V] Jet V (Fin n × Fin d) m))) z J := by
  rw [← spMap_spMap]
  exact val_pull hJ _ _ _

end Frame

theorem isPtCube_of_isFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t : SAB H (Sp V)) (d : ℕ) (F : Fin d → PS V 2 d) (act : 𝓞 E → Fin d → PS V 1 d) (ph1 ph2 : PS V 3 d) (sy : PS V 2 d) (ad : 𝓞 E → PS V 2 d) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m), IsFrameG t (𝟙 (Sp V)) d x F act ph1 ph2 sy ad e → (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → ∀ (Ω : Type) [Field Ω] (β : V →+* Ω) (P : PtFam (spMap β) t.G d), IsJetPt β x P → IsPtCube (spMap β) t.G t.cub (fun j => MvPowerSeries.map β (F j)) (MvPowerSeries.map β ph1) (MvPowerSeries.map β ph2) P := by
  intro E _ _ _ H V _ t d F act ph1 ph2 sy ad x e hfr hF Ω _ β P hP A _ _ I hI z J hJ
  obtain ⟨m, hm⟩ := id hI
  have hm' : I ^ (m + 1) = ⊥ := by rw [pow_succ, hm, zero_mul]; rfl
  obtain ⟨e', he'⟩ := exists_val (A := A) β (e m) z J
  refine ⟨e', fun a b u ha hb hu => ?_⟩
  obtain ⟨ψ, ⟨hψ, hX⟩, -⟩ := (GlobalTheory.T.jetRing_hom_exists_unique_spec V Ω A β (Fin 3 × Fin d) m).1 (fun q => ![a, b, u] q.1 q.2) (by
    refine le_bot_iff.1 (le_trans (Ideal.pow_right_mono (Ideal.span_le.2 ?_) _) hm'.le)
    rintro _ ⟨⟨i, j⟩, rfl⟩
    fin_cases i
    exacts [ha j, hb j, hu j])
  have hpe : ∀ (φ : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) V) (v w : Fin d → A),
      (∀ i j, MvPolynomial.constantCoeff (φ i j) = 0) → (∀ j, ψ (Ideal.Quotient.mk _ (φ 0 j)) = v j) →
      (∀ j, ψ (Ideal.Quotient.mk _ (φ 1 j)) = w j) → val (peG t (𝟙 _) d x e m φ) (spMap ψ) z J = e' v w :=
    fun φ v w h h₀ h₁ => (val_pe e hJ ψ φ).trans (he' _
      (fun v => by simp only [RingHom.comp_apply, RingHom.coe_coe, AlgHom.commutes, hψ]) v w
      (fun j => (congrArg ψ (subst_X (fun p : Fin 2 × Fin d => φ p.1 p.2) (0, j) (h 0 j))).trans (h₀ j))
      (fun j => (congrArg ψ (subst_X (fun p : Fin 2 × Fin d => φ p.1 p.2) (1, j) (h 1 j))).trans (h₁ j)))
  have hXX : ∀ i k : Fin 3, val (peG t (𝟙 _) d x e m ![fun j => MvPolynomial.X (i, j), fun j => MvPolynomial.X (k, j)])
      (spMap ψ) z J = e' (![a, b, u] i) (![a, b, u] k) := fun i k =>
    hpe _ _ _ (fun l j => by fin_cases l <;> simp) (fun j => hX (i, j)) (fun j => hX (k, j))
  have hadd : ∀ (i k : Fin 3) (j : Fin d), ψ (Ideal.Quotient.mk _ (psIn d m ![i, k] (F j))) =
      addP (fun j => MvPowerSeries.map β (F j)) (![a, b, u] i) (![a, b, u] k) j := fun i k j => by
    rw [map_psIn ψ hψ, addP]
    congr 1
    funext l j'
    rw [hX]
    fin_cases l <;> rfl
  have hpt : ∀ i : Fin 3, ptOf ψ hψ ≫ jptG t (𝟙 _) d x m i = P A (![a, b, u] i) := fun i => by
    rw [ptOf_jpt hP]
    exact congrArg (P A) (funext fun j => hX (i, j))
  have hsc : ∀ (ph : PS V 3 d) (w : (Jet V (Fin 3 × Fin d) m)ˣ), (w : Jet V (Fin 3 × Fin d) m) = psJet m ph →
      (gm (spMap ψ) z ⊤ (unitΓ w)).val =
        gs (𝟙 (Sp A)) z ⊤ (toΓ A (evP ![a, b, u] (MvPowerSeries.map β ph))) := fun ph w hw => by
    rw [gm_unit, hw, ((GlobalTheory.T.jetRing_hom_exists_unique_spec V Ω A β (Fin 3 × Fin d) m).2 ψ hψ).2.2 ph, evP]
    simp only [hX]
  constructor
  · obtain ⟨w, hw, hc⟩ := hfr.ph1 m
    have k := (val_cub t.cub (ptOf ψ hψ) hJ _ _ _).symm.trans ((val_corr hJ hc (spMap ψ)).trans
      ((GlobalTheory.UU.val_scaleGen _ _ _ hJ).trans (congrArg₂ (· * ·) rfl ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        (hpe _ _ _ (fun l j => by fin_cases l; exacts [cc_psIn _ _ (hF j), MvPolynomial.constantCoeff_X _ _])
          (hadd 0 1) (fun j => hX (2, j)))
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_inv _ _).trans (congrArg (·⁻¹) (hXX 0 2)))
          ((val_inv _ _).trans (congrArg (·⁻¹) (hXX 1 2))))))))))
    rw [hpt, hpt, hpt] at k
    have k' : cubV t.cub z J (P A a) (P A b) (P A u) = gm (spMap ψ) z ⊤ (unitΓ w) *
      (e' (addP (fun j => MvPowerSeries.map β (F j)) a b) u * ((e' a u)⁻¹ * (e' b u)⁻¹)) := k
    refine Eq.trans ?_ (congrArg (· * _) (hsc ph1 w hw))
    refine Eq.trans (congrArg Units.val ?_) (Units.val_mul _ _)
    rw [k']
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · obtain ⟨w, hw, hc⟩ := hfr.ph2 m
    have k := (val_cub t.cub (ptOf ψ hψ) hJ _ _ _).symm.trans ((val_corr hJ hc (spMap ψ)).trans
      ((GlobalTheory.UU.val_scaleGen _ _ _ hJ).trans (congrArg₂ (· * ·) rfl ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
        (hpe _ _ _ (fun l j => by fin_cases l; exacts [MvPolynomial.constantCoeff_X _ _, cc_psIn _ _ (hF j)])
          (fun j => hX (0, j)) (hadd 1 2))
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_inv _ _).trans (congrArg (·⁻¹) (hXX 0 1)))
          ((val_inv _ _).trans (congrArg (·⁻¹) (hXX 0 2))))))))))
    rw [hpt, hpt, hpt] at k
    have k' : cubV t.cub z J (P A b) (P A u) (P A a) = gm (spMap ψ) z ⊤ (unitΓ w) *
      (e' a (addP (fun j => MvPowerSeries.map β (F j)) b u) * ((e' a b)⁻¹ * (e' a u)⁻¹)) := k
    refine Eq.trans ?_ (congrArg (· * _) (hsc ph2 w hw))
    refine Eq.trans (congrArg Units.val ?_) (Units.val_mul _ _)
    rw [k']
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

end GlobalTheory.AlphaPair.Cube
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FramePartialLawsNilpotentCoordinatesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_partial_laws_nilpotent_coordinates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t : SAB H (Sp V)) (d : ℕ) (F : Fin d → PS V 2 d) (act : 𝓞 E → Fin d → PS V 1 d) (ph1 ph2 : PS V 3 d) (sy : PS V 2 d) (ad : 𝓞 E → PS V 2 d) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m), IsFrameG t (𝟙 (Sp V)) d x F act ph1 ph2 sy ad e → (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → ∀ (Ω : Type) [Field Ω] (β : V →+* Ω) (P : PtFam (spMap β) t.G d), IsJetPt β x P → IsPtCube (spMap β) t.G t.cub (fun j => MvPowerSeries.map β (F j)) (MvPowerSeries.map β ph1) (MvPowerSeries.map β ph2) P := by
  first | exact @GlobalTheory.AlphaPair.Cube.isPtCube_of_isFrame | exact GlobalTheory.AlphaPair.Cube.isPtCube_of_isFrame | (intros; apply GlobalTheory.AlphaPair.Cube.isPtCube_of_isFrame <;> assumption)
end
end
