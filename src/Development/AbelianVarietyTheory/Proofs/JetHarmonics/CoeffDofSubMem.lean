module

public import Development.AbelianVarietyTheory.Definitions.Jets.ColValMonomial
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsGenRosati
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicCompleteOfFiniteBasis
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.GermEvalOneStandardPointSelf
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsGoodConst
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SubstMapAlgebraMap
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HasSubstAddSqZero
set_option autoImplicit false

noncomputable section

open MvPowerSeries
open scoped MvPowerSeries.WithPiTopology
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.Jets

theorem hasSubst_add_sqZero {σ τ S : Type} [Fintype σ] [CommRing S]
    (a b : σ → MvPowerSeries τ S) (e : MvPowerSeries τ S) (he : e * e = 0)
    (ha : ∀ s, IsNilpotent (constantCoeff (a s))) : HasSubst (fun s => a s + e * b s) := by
  apply hasSubst_of_constantCoeff_nilpotent
  intro s
  rw [map_add (f := _), map_mul]
  have h1 : IsNilpotent (constantCoeff e) := ⟨2, by rw [pow_two, ← map_mul, he, map_zero]⟩
  exact (Commute.all _ _).isNilpotent_add (ha s) ((Commute.all _ _).isNilpotent_mul_right h1)

theorem subst_add_sqZero {σ τ S : Type} [Fintype σ] [CommRing S]
    (a b : σ → MvPowerSeries τ S) (e : MvPowerSeries τ S) (he : e * e = 0)
    (ha0 : ∀ s, IsNilpotent (constantCoeff (a s))) (g : MvPowerSeries σ S) :
    subst (fun s => a s + e * b s) g = subst a g + e * ∑ s, b s * subst a (pderiv s g) := by
  classical
  letI : TopologicalSpace S := ⊥
  letI : UniformSpace S := ⊥
  haveI : DiscreteUniformity S := ⟨rfl⟩
  have ha : HasSubst a := hasSubst_of_constantCoeff_nilpotent ha0
  have hb : HasSubst (fun s => a s + e * b s) := hasSubst_add_sqZero a b e he ha0
  have continuousPderiv (i : σ) : Continuous (fun f : MvPowerSeries σ S => pderiv i f) := by
    refine continuous_pi fun n => ?_
    have h : (fun f : MvPowerSeries σ S => (pderiv i f) n) =
        (fun a : S => a * ((n i : S) + 1)) ∘ ⇑(MvPowerSeries.coeff (n + Finsupp.single i 1)) := by
      funext f
      exact coeff_pderiv f n
    rw [h]
    exact continuous_of_discreteTopology.comp (MvPowerSeries.WithPiTopology.continuous_coeff S _)
  have hca : Continuous (subst a : MvPowerSeries σ S → MvPowerSeries τ S) := continuous_subst ha
  have hcb : Continuous (subst (fun s => a s + e * b s) :
      MvPowerSeries σ S → MvPowerSeries τ S) := continuous_subst hb
  have hs0 : subst a (0 : MvPowerSeries σ S) = 0 := by rw [← coe_substAlgHom ha, map_zero]
  have hs1 : subst a (1 : MvPowerSeries σ S) = 1 := by rw [← coe_substAlgHom ha, map_one]
  let D2 : MvPowerSeries σ S → MvPowerSeries τ S := fun g =>
    subst a g + e * ∑ s, b s * subst a (pderiv s g)
  have c2 : Continuous D2 :=
    hca.add (continuous_const.mul (continuous_finsetSum _ fun i _ =>
      continuous_const.mul (hca.comp (continuousPderiv _))))
  have hpoly : ∀ p : MvPolynomial σ S,
      subst (fun s => a s + e * b s) (MvPolynomial.toMvPowerSeries p) = D2 (MvPolynomial.toMvPowerSeries p) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C r => simp [D2, subst_C, hs0]
    | add p q hp hq =>
      simp only [D2, MvPolynomial.coe_add, subst_add ha, subst_add hb, map_add (f := _)] at hp hq ⊢
      rw [hp, hq]
      simp only [mul_add, Finset.sum_add_distrib]
      ring
    | mul_X p s hp =>
      simp only [D2, MvPolynomial.coe_mul, MvPolynomial.coe_X] at hp ⊢
      rw [subst_mul ha, subst_X ha, subst_mul hb, subst_X hb, hp]
      have hX : ∀ i : σ, pderiv i (X s : MvPowerSeries σ S) = if i = s then 1 else 0 := by
        intro i
        by_cases h : i = s
        · subst h; simp
        · rw [if_neg h, pderiv_X_of_ne]
          intro h'
          exact h h'.symm
      have hterm : ∀ i : σ, b i * subst a (pderiv i ((MvPolynomial.toMvPowerSeries p) * X s)) =
          (if i = s then b i * subst a (MvPolynomial.toMvPowerSeries p) else 0) +
            a s * (b i * subst a (pderiv i (MvPolynomial.toMvPowerSeries p))) := by
        intro i
        rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hX i, subst_add ha, subst_mul ha,
          subst_mul ha, subst_X ha]
        split_ifs with h
        · rw [hs1]; ring
        · rw [hs0]; ring
      rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib, Finset.sum_ite_eq',
        if_pos (Finset.mem_univ _), ← Finset.mul_sum]
      linear_combination (b s * ∑ i, b i * subst a (pderiv i (MvPolynomial.toMvPowerSeries p))) * he
  have := (MvPowerSeries.WithPiTopology.denseRange_toMvPowerSeries).equalizer hcb c2 (funext fun p => hpoly p)
  exact congrFun this g

theorem map_pderiv' {σ R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (i : σ)
    (f : MvPowerSeries σ R) :
    MvPowerSeries.map φ (pderiv i f) = pderiv i (MvPowerSeries.map φ f) := by
  classical
  ext n
  simp [coeff_pderiv]

theorem hasSubst_pt_zero (R : Type) [CommRing R] (d : ℕ) :
    ∀ p : Fin 2 × Fin d,
      constantCoeff ((![pt R d 0, 0] : Fin 2 → Pt R 1 d) p.1 p.2) = 0 := by
  rintro ⟨j, i⟩
  fin_cases j <;> simp [pt]

theorem law_right_unit {R : Type} [CommRing R] {d : ℕ} (G : FGLaw R d) (i : Fin d) :
    ev (n := 1) ![pt R d 0, 0] (G.F i) = (X ((0 : Fin 1), i) : PS R 1 d) := by
  have hb : HasSubst (fun p : Fin 2 × Fin d => (![pt R d 0, 0] : Fin 2 → Pt R 1 d) p.1 p.2) :=
    hasSubst_of_constantCoeff_zero (hasSubst_pt_zero R d)
  have ha : HasSubst
      (fun p : Fin 2 × Fin d => (![pt R d 1, pt R d 0] : Fin 2 → Pt R 2 d) p.1 p.2) :=
    hasSubst_of_constantCoeff_zero (by
      rintro ⟨j, i⟩
      fin_cases j <;> simp [pt])
  rw [← G.comm i, ← G.unit i]
  unfold ev
  rw [subst_comp_subst_apply ha hb]
  congr 1
  funext p
  obtain ⟨j, l⟩ := p
  fin_cases j
  · exact subst_X hb ((1 : Fin 2), l)
  · exact subst_X hb ((0 : Fin 2), l)

theorem map_ev_pt_zero {R S : Type} [CommRing R] [CommRing S] {d : ℕ} (φ : R →+* S)
    (g : PS R 2 d) :
    MvPowerSeries.map φ (ev (n := 1) ![pt R d 0, 0] g) =
      ev (n := 1) ![pt S d 0, 0] (MvPowerSeries.map φ g) := by
  unfold ev
  rw [MvPowerSeries.map_subst (hasSubst_of_constantCoeff_zero (hasSubst_pt_zero R d))]
  congr 1
  funext p
  obtain ⟨j, l⟩ := p
  fin_cases j <;> simp [pt]

theorem C_eps_mul_self (R : Type) [CommRing R] (τ : Type) :
    (C (DualNumber.eps : DualNumber R) : MvPowerSeries τ (DualNumber R)) * C DualNumber.eps = 0 := by
  rw [← map_mul, DualNumber.eps_mul_eps, map_zero]

theorem addOf_eps {R : Type} [CommRing R] {d : ℕ} (G : FGLaw R d) (v : Fin d → R) (j : Fin d) :
    addOf (n := 1) (G.mapF (algebraMap R (DualNumber R))) (pt (DualNumber R) d 0)
        (fun i => C (TrivSqZeroExt.inr (v i) : DualNumber R)) j =
      X ((0 : Fin 1), j) + C (DualNumber.eps : DualNumber R) *
        MvPowerSeries.map (algebraMap R (DualNumber R))
          (∑ i : Fin d, C (v i) *
            ev (n := 1) ![pt R d 0, 0] (pderiv ((1 : Fin 2), i) (G.F j))) := by
  have h := subst_add_sqZero
    (fun p : Fin 2 × Fin d => (![pt (DualNumber R) d 0, 0] : Fin 2 → Pt (DualNumber R) 1 d) p.1 p.2)
    (fun p : Fin 2 × Fin d => (![0, fun i => C (algebraMap R (DualNumber R) (v i))] :
      Fin 2 → Pt (DualNumber R) 1 d) p.1 p.2)
    (C DualNumber.eps) (C_eps_mul_self R _)
    (fun p => by rw [hasSubst_pt_zero]; exact IsNilpotent.zero)
    (MvPowerSeries.map (algebraMap R (DualNumber R)) (G.F j))
  have h1 := map_ev_pt_zero (algebraMap R (DualNumber R)) (G.F j)
  rw [law_right_unit, map_X] at h1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, map_sum]
  simp only [map_mul, map_C, map_ev_pt_zero, map_pderiv']
  rw [Fintype.sum_prod_type, Fin.sum_univ_two] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply, zero_mul,
    Finset.sum_const_zero, zero_add] at h
  refine Eq.trans ?_ h
  unfold addOf ev FGLaw.mapF
  congr 1
  funext p
  obtain ⟨l, i⟩ := p
  fin_cases l
  · simp
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, Pi.zero_apply,
      zero_add]
    rw [← map_mul]
    congr 1
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem ev_addOf_eps :
    ∀ (R : Type) [CommRing R] (d : ℕ) (G : FGLaw R d) (v : Fin d → R) (f : PS R 1 d),
      ev (n := 1) ![addOf (G.mapF (algebraMap R (DualNumber R))) (pt (DualNumber R) d 0)
          (fun i => C (TrivSqZeroExt.inr (v i) : DualNumber R))]
        (MvPowerSeries.map (algebraMap R (DualNumber R)) f) =
      MvPowerSeries.map (algebraMap R (DualNumber R)) f +
        C (DualNumber.eps : DualNumber R) *
          MvPowerSeries.map (algebraMap R (DualNumber R)) (Dof G.F v f) := by
  intro R _ d G v f
  have h := subst_add_sqZero
    (X : Fin 1 × Fin d → PS (DualNumber R) 1 d)
    (fun p : Fin 1 × Fin d => MvPowerSeries.map (algebraMap R (DualNumber R))
          (∑ i : Fin d, C (v i) *
            ev (n := 1) ![pt R d 0, 0] (pderiv ((1 : Fin 2), i) (G.F p.2))))
    (C DualNumber.eps) (C_eps_mul_self R _)
    (fun p => by rw [constantCoeff_X]; exact IsNilpotent.zero)
    (MvPowerSeries.map (algebraMap R (DualNumber R)) f)
  rw [subst_self, Fintype.sum_prod_type, Fin.sum_univ_one] at h
  unfold Dof
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_mul (MvPowerSeries.map (algebraMap R (DualNumber R)))
    (∑ i : Fin d, _) (pderiv (R := R) _ f), map_pderiv' (algebraMap R (DualNumber R)) _ f]
  refine Eq.trans ?_ h
  unfold ev
  congr 1
  funext p
  obtain ⟨l, j⟩ := p
  obtain rfl : l = 0 := Subsingleton.elim _ _
  exact addOf_eps G v j

end GlobalTheory.Jets
end
end

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε LPow ThetaGrp IsActOf WeilIs translT GlobalFnsSt)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Good val sval gs)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EigenDer

variable {R : Type} [CommRing R]

theorem exists_jet_factor {κ A : Type} [Finite κ] [CommRing A] [Algebra R A] (T : MvPowerSeries κ R →ₐ[R] A)
    (hT : ∀ p, IsNilpotent (T (X p))) :
    ∃ (n : ℕ) (Θ : JetR R κ (n + 1) →ₐ[R] A), ∀ g, Θ (toJet (n + 1) g) = T g := by
  let J : Ideal A := Ideal.span (Set.range fun p => T (X p))
  have hfg : J.FG := Submodule.fg_span (Set.finite_range _)
  have hn : IsNilpotent J := (Ideal.FG.isNilpotent_iff_le_nilradical hfg).2 (by
    rw [Ideal.span_le]
    rintro _ ⟨p, rfl⟩
    exact hT p)
  obtain ⟨n, hn⟩ := hn
  have hJ : J ^ (n + 1 + 1) = ⊥ := by
    rw [add_assoc, pow_add, hn, zero_mul, Ideal.zero_eq_bot]
  have hm : ∀ p, T (X p) ∈ J := fun p => Ideal.subset_span ⟨p, rfl⟩
  refine ⟨n, jetLift R J hJ (fun p => T (X p)) hm, fun g => ?_⟩
  have h := GlobalTheory.algHom_sub_aeval_truncTotal_mem T hm (n + 1 + 1) g
  rw [hJ, Ideal.mem_bot, sub_eq_zero] at h
  exact h.symm

theorem exists_trunc_one {G : Over (Spec (CommRingCat.of R))} {κ : Type} (x : Fam G κ)
    (hx : ∀ m, spMap (jetTruncR R κ m) ≫ x (m + 1) = x m) (n : ℕ) :
    ∃ t : JetR R κ (n + 1) →ₐ[R] JetR R κ 1, (∀ j, t (zR (n + 1) j) = zR 1 j) ∧ spMap t ≫ x (n + 1) = x 1 := by
  induction n with
  | zero =>
    refine ⟨AlgHom.id R _, fun _ => rfl, ?_⟩
    have : spMap (R₀ := R) (AlgHom.id R (JetR R κ 1)) = 𝟙 _ := by
      apply Over.OverMorphism.ext
      rw [spMap_left]
      exact Spec.map_id _
    rw [this, Category.id_comp]
  | succ n ih =>
    obtain ⟨t, h1, h2⟩ := ih
    refine ⟨t.comp (jetTruncR R κ (n + 1)), fun j => h1 j, ?_⟩
    rw [← spMap_comp, Category.assoc, hx, h2]

theorem subst_map_algebraMap {σ τ S : Type} [Finite σ] [CommRing S] [Algebra R S] {a : σ → MvPowerSeries τ S}
    (ha : HasSubst a) (f : MvPowerSeries σ R) :
    subst a (MvPowerSeries.map (algebraMap R S) f) = subst a f := by
  rw [map_algebraMap_eq_subst_X, subst_comp_subst_apply HasSubst.X ha]
  congr 1
  funext s
  exact subst_X ha s

def tanPair (d : ℕ) (v : Fin d → R) : Fin 2 × Fin d → PS (DualNumber R) 1 d := fun p =>
  (![pt (DualNumber R) d 0, fun i => C (TrivSqZeroExt.inr (v i) : DualNumber R)] :
    Fin 2 → Pt (DualNumber R) 1 d) p.1 p.2

theorem inr_nilpotent (r : R) : IsNilpotent (TrivSqZeroExt.inr r : DualNumber R) :=
  ⟨2, by rw [pow_two, TrivSqZeroExt.inr_mul_inr]⟩

theorem hasSubst_tanPair (d : ℕ) (v : Fin d → R) : HasSubst (tanPair d v) := by
  apply hasSubst_of_constantCoeff_nilpotent
  rintro ⟨j, i⟩
  fin_cases j
  · simp [tanPair, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt]
  · simpa [tanPair] using inr_nilpotent (v i)

theorem ev_pt_pt {d : ℕ} (g : PS R 2 d) : ev (n := 2) ![pt R d 0, pt R d 1] g = g := by
  have : (fun p : Fin 2 × Fin d => (![pt R d 0, pt R d 1] : Fin 2 → Pt R 2 d) p.1 p.2) = X := by
    funext p
    obtain ⟨j, i⟩ := p
    fin_cases j <;> rfl
  unfold ev
  rw [this, subst_self, id]

theorem subst_tanPair_fst {d : ℕ} (v : Fin d → R) (f : PS R 1 d) :
    subst (tanPair d v) (ev (n := 2) ![pt R d 0] f) = MvPowerSeries.map (algebraMap R (DualNumber R)) f := by
  have ha : HasSubst (fun p : Fin 1 × Fin d => (![pt R d 0] : Fin 1 → Pt R 2 d) p.1 p.2) :=
    hasSubst_of_constantCoeff_zero (by
      rintro ⟨j, i⟩
      fin_cases j
      simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt])
  unfold ev
  rw [subst_comp_subst_apply ha (hasSubst_tanPair d v), map_algebraMap_eq_subst_X]
  congr 1
  funext p
  obtain ⟨j, i⟩ := p
  fin_cases j
  exact subst_X (hasSubst_tanPair d v) ((0 : Fin 2), i)

theorem subst_tanPair_add {d : ℕ} (Gl : FGLaw R d) (v : Fin d → R) (f : PS R 1 d) :
    subst (tanPair d v) (ev (n := 2) ![addOf Gl.F (pt R d 0) (pt R d 1)] f) =
      MvPowerSeries.map (algebraMap R (DualNumber R)) f +
        C (DualNumber.eps : DualNumber R) *
          MvPowerSeries.map (algebraMap R (DualNumber R)) (Dof Gl.F v f) := by
  have hF : addOf (n := 2) Gl.F (pt R d 0) (pt R d 1) = Gl.F := funext fun i => ev_pt_pt _
  have ha : HasSubst (fun p : Fin 1 × Fin d => (![Gl.F] : Fin 1 → Pt R 2 d) p.1 p.2) :=
    hasSubst_of_constantCoeff_zero (by
      rintro ⟨j, i⟩
      fin_cases j
      exact Gl.const i)
  have e : (fun p : Fin 1 × Fin d => subst (tanPair d v) ((![Gl.F] : Fin 1 → Pt R 2 d) p.1 p.2)) =
      fun p : Fin 1 × Fin d => (![addOf (Gl.mapF (algebraMap R (DualNumber R))) (pt (DualNumber R) d 0)
          (fun i => C (TrivSqZeroExt.inr (v i) : DualNumber R))] : Fin 1 → Pt (DualNumber R) 1 d) p.1 p.2 := by
    funext p
    obtain ⟨j, i⟩ := p
    fin_cases j
    exact (subst_map_algebraMap (hasSubst_tanPair d v) (Gl.F i)).symm
  have hc := ha.comp (hasSubst_tanPair d v)
  simp only [substAlgHom_apply] at hc
  rw [← GlobalTheory.Jets.ev_addOf_eps, hF]
  unfold ev
  rw [subst_comp_subst_apply ha (hasSubst_tanPair d v), ← e, subst_map_algebraMap hc]

theorem dof_eq_of_eigen : JetAlgSt → RepSt → SerSt → ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (d : ℕ) (x : Fam G (Fin d)), IsUnivChart G d x → ∀ Gl : FGLaw R d, IsLawOf x Gl.F → ∀ (U : G.left.Opens), ⊤ ≤ η[G].left ⁻¹ᵁ U → ∀ (s : Γ(G.left, U)) (f : PS R 1 d), IsSer1 x U s f → ∀ (v : Fin d → R) (y : R) (φ : JetR R (Fin d) 1 →ₐ[R] DualNumber R), (∀ i, φ (zR 1 i) = TrivSqZeroExt.inr (v i)) → (∀ (A : Type) [CommRing A] [Algebra R A] (c : DualNumber R →ₐ[R] A) (r : sp (R₀ := R) A ⟶ G), ⊤ ≤ r.left ⁻¹ᵁ U → ⊤ ≤ (r * (spMap c ≫ spMap φ ≫ x 1)).left ⁻¹ᵁ U → fnVal (r * (spMap c ≫ spMap φ ≫ x 1)).left U s = c (1 + TrivSqZeroExt.inr y) * fnVal r.left U s) → Dof Gl.F v f = C y * f := by
  intro _ hRep _ R _ G _ d x hx Gl hl U _ s f hf v y φ hφ H
  have hb := hasSubst_tanPair d v
  have hpt : ∀ (k : Fin 2) (j : Fin d), constantCoeff (pt R (n := 2) d k j) = 0 := fun k j => by
    simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt]
  obtain ⟨y₁, hy₁, -⟩ := (hRep R G d x hx (Fin 2 × Fin d)).1 (pt R d 0) (hpt 0)
  obtain ⟨y₂, hy₂, -⟩ := (hRep R G d x hx (Fin 2 × Fin d)).1 (pt R d 1) (hpt 1)
  have s₁ := hf 2 _ _ hy₁
  have s₁₂ := hf 2 _ _ (hl.2 2 _ _ _ _ hy₁ hy₂)
  have key : subst (tanPair d v) (ev (n := 2) ![addOf Gl.F (pt R d 0) (pt R d 1)] f) =
      C (1 + TrivSqZeroExt.inr y : DualNumber R) * subst (tanPair d v) (ev (n := 2) ![pt R d 0] f) := by
    refine eq_of_toJet_eq fun m => ?_
    let T : PS R 2 d →ₐ[R] JetR (DualNumber R) (Fin 1 × Fin d) m :=
      ((toJetHom (DualNumber R) (Fin 1 × Fin d) m).restrictScalars R).comp (substAlgHom hb)
    have hT : ∀ g, T g = toJet m (subst (tanPair d v) g) := fun g => by
      rw [← substAlgHom_apply hb]; rfl
    let c : DualNumber R →ₐ[R] JetR (DualNumber R) (Fin 1 × Fin d) m := IsScalarTower.toAlgHom R _ _
    have hc : ∀ a, toJet m (C a : PS (DualNumber R) 1 d) = c a := fun a =>
      (toJetHom (DualNumber R) (Fin 1 × Fin d) m).commutes a
    have hT1 : ∀ i, T (X ((1 : Fin 2), i)) = c (TrivSqZeroExt.inr (v i)) := fun i => by
      rw [hT, subst_X hb, ← hc]; rfl
    have hT0 : ∀ i, T (X ((0 : Fin 2), i)) = zR m ((0 : Fin 1), i) := fun i => by
      rw [hT, subst_X hb, ← toJet_X]; rfl
    obtain ⟨n, Θ, hΘ⟩ := exists_jet_factor T (by
      rintro ⟨j, i⟩
      fin_cases j
      · refine hT0 i ▸ ⟨m + 1, ?_⟩
        have := Ideal.pow_mem_pow (zR_mem_ker (R := DualNumber R) m ((0 : Fin 1), i)) (m + 1)
        rwa [ker_jetAug_pow, Ideal.mem_bot] at this
      · exact hT1 i ▸ (inr_nilpotent (v i)).map c)
    obtain ⟨t, ht, htx⟩ := exists_trunc_one x hx.1 n
    obtain ⟨ψ, hψ, hψy⟩ := hy₂.2 (n + 1)
    have e₂ : spMap c ≫ spMap φ ≫ x 1 = spMap Θ ≫ y₂ (n + 1) := by
      have : c.comp (φ.comp t) = Θ.comp ψ := jet_ext fun j => by
        rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, ht, hφ, hψ, hΘ]
        exact (hT1 j).symm
      rw [hψy, ← htx, ← Category.assoc (spMap φ), spMap_comp, ← Category.assoc, spMap_comp, this,
        ← Category.assoc, spMap_comp]
    have e : (spMap Θ ≫ y₁ (n + 1)) * (spMap c ≫ spMap φ ≫ x 1) = spMap Θ ≫ (y₁ (n + 1) * y₂ (n + 1)) := by
      rw [e₂, MonObj.comp_mul]
    have h := H _ c (spMap Θ ≫ y₁ (n + 1)) (top_le_preimage_comp _ _ U (s₁ (n + 1)).1)
      (by rw [e]; exact top_le_preimage_comp _ _ U (s₁₂ (n + 1)).1)
    have v₁ := fnVal_specMap Θ.toRingHom _ U (s₁ (n + 1)).1 s
    have v₁₂ := fnVal_specMap Θ.toRingHom _ U (s₁₂ (n + 1)).1 s
    rw [(s₁ (n + 1)).2] at v₁
    rw [(s₁₂ (n + 1)).2] at v₁₂
    rw [e] at h
    have h' := v₁₂.symm.trans (h.trans (congrArg (c (1 + TrivSqZeroExt.inr y) * ·) v₁))
    rw [← toJetHom_apply m (C _ * _), map_mul, toJetHom_apply, toJetHom_apply, hc, ← hT, ← hT, ← hΘ, ← hΘ]
    exact h'
  rw [subst_tanPair_add, subst_tanPair_fst] at key
  ext e
  have := congrArg (fun g => TrivSqZeroExt.snd (coeff e g)) key
  simp only [map_add (coeff e), coeff_C_mul, coeff_map] at this
  simpa [TrivSqZeroExt.algebraMap_eq_inl] using this

end GlobalTheory.EigenDer
end
end

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.Out (scal resTop)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (IsGrpPullback pushHom isGrpPullback_pullback)
open ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EigenGerm

section Values

variable {A R : Type} [CommRing A] [CommRing R] {X : Scheme.{0}}

theorem fnVal_const (p : Spec (CommRingCat.of A) ⟶ X) (π : X ⟶ Spec (CommRingCat.of R)) (θ : R →+* A)
    (hp : p ≫ π = Spec.map (CommRingCat.ofHom θ)) (U : X.Opens) (h : ⊤ ≤ p ⁻¹ᵁ U) (c : R) :
    fnVal p U (resTop U (scal π c)) = θ c := by
  refine (fnVal_res p U ⊤ le_top h _).2.symm.trans ?_
  refine (ChartBaseChange.fnVal_comp p π ⊤ _).trans ?_
  rw [hp, ← Category.comp_id (Spec.map _), fnVal_specMap θ _ ⊤ le_top]
  congr 1
  unfold fnVal
  rw [dite_eq_left (show ⊤ ≤ (𝟙 (Spec (CommRingCat.of R)) : _ ⟶ _) ⁻¹ᵁ ⊤ from le_top)]
  have e : (𝟙 (Spec (CommRingCat.of R)) : _ ⟶ _).appLE ⊤ ⊤ le_top = 𝟙 _ := by
    simp [Scheme.Hom.appLE]
  rw [e]
  exact congrArg (fun q => q.hom c) (Scheme.ΓSpecIso (CommRingCat.of R)).inv_hom_id

variable {G : Over (Spec (CommRingCat.of R))} {d : ℕ} {x : Fam G (Fin d)} {U : G.left.Opens}

theorem exists_evHom {m n : ℕ} {a : Fin m → Pt R n d} (ha : ∀ j i, constantCoeff (a j i) = 0) :
    ∃ Ψ : PS R m d →ₐ[R] PS R n d, ∀ f, ev a f = Ψ f :=
  ⟨MvPowerSeries.substAlgHom (R := R) (FBMap.hasSubst_of ha),
    fun f => (congrFun (MvPowerSeries.coe_substAlgHom (FBMap.hasSubst_of ha)) f).symm⟩

theorem isSer1_mul (hJ : JetAlgSt) {f f' : Γ(G.left, U)} {g g' : PS R 1 d} (h : IsSer1 x U f g)
    (h' : IsSer1 x U f' g') : IsSer1 x U (f * f') (g * g') := by
  intro n a y hy m
  obtain ⟨τ, hτ, -⟩ := (hJ R (Fin n × Fin d)).1 m
  obtain ⟨Ψ, hΨ⟩ := exists_evHom (a := ![a]) (single_point_zero_constant hy.1)
  obtain ⟨h₁, h₂⟩ := h n a y hy m
  obtain ⟨-, h₃⟩ := h' n a y hy m
  refine ⟨h₁, ?_⟩
  rw [fnVal_eq_fnValHom _ _ h₁] at h₂ h₃ ⊢
  rw [map_mul, h₂, h₃, hΨ, hΨ, hΨ, map_mul, ← hτ, ← hτ, ← hτ, map_mul]

theorem isSer1_mul_pow (hJ : JetAlgSt) {f f' : Γ(G.left, U)} {g g' : PS R 1 d} (h : IsSer1 x U f g)
    (h' : IsSer1 x U f' g') (k : ℕ) : IsSer1 x U (f * f' ^ k) (g * g' ^ k) := by
  induction k with
  | zero => simpa only [pow_zero, _root_.mul_one] using h
  | succ k ih =>
    rw [pow_succ, pow_succ, ← _root_.mul_assoc, ← _root_.mul_assoc]
    exact isSer1_mul hJ ih h'

theorem isSer1_res {W : G.left.Opens} (hle : U ≤ W) {f : Γ(G.left, W)} {g : PS R 1 d}
    (h : IsSer1 x U ((G.left.presheaf.map (homOfLE hle).op).hom f) g) : IsSer1 x W f g := by
  intro n a y hy m
  obtain ⟨h₁, h₂⟩ := h n a y hy m
  obtain ⟨h₃, h₄⟩ := fnVal_res _ U W hle h₁ f
  exact ⟨h₃, h₄.trans h₂⟩

end Values

section BaseChange

variable {V R : Type} [CommRing V] [CommRing R] [Algebra V R]

theorem dof_baseChange (hJ : JetAlgSt) (hRep : RepSt) (hSer : SerSt) [IsLocalRing V]
    {G : Over (Spec (CommRingCat.of V))} [GrpObj G] {d : ℕ} {x : Fam G (Fin d)} (hx : IsUnivChart G d x)
    (Gl : FGLaw V d) (hGl : IsLawOf x Gl.F) {U : G.left.Opens} (hU : ⊤ ≤ η[G].left ⁻¹ᵁ U) {l : ℕ}
    (s : Fin l → Γ(G.left, U)) (S : Fin l → PS V 1 d) (hS : ∀ i, IsSer1 x U (s i) (S i)) (c : Fin l → R)
    (v : Fin d → R) (y : R) (φ : JetR V (Fin d) 1 →ₐ[V] DualNumber R)
    (hφ : ∀ i, φ (zR 1 i) = TrivSqZeroExt.inr (v i))
    (H : ∀ (A : Type) [CommRing A] [Algebra V A] (θ : DualNumber R →ₐ[V] A) (r : sp (R₀ := V) A ⟶ G),
      ⊤ ≤ r.left ⁻¹ᵁ U → ⊤ ≤ (r * (spMap θ ≫ spMap φ ≫ x 1)).left ⁻¹ᵁ U →
      ∑ i, θ (TrivSqZeroExt.inl (c i)) * fnVal (r * (spMap θ ≫ spMap φ ≫ x 1)).left U (s i) =
        θ (1 + TrivSqZeroExt.inr y) * ∑ i, θ (TrivSqZeroExt.inl (c i)) * fnVal r.left U (s i)) :
    Dof (fun i => MvPowerSeries.map (algebraMap V R) (Gl.F i)) v
        (∑ i, C (c i) * MvPowerSeries.map (algebraMap V R) (S i)) =
      C y * ∑ i, C (c i) * MvPowerSeries.map (algebraMap V R) (S i) := by
  let G' := (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap V R)))).obj G
  let π : G'.left ⟶ G.left := pullback.fst _ _
  have hπ : IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap V R))) π := isGrpPullback_pullback _ _
  choose x' hx' using fun m => ChartBaseChange.push_surjective hπ
    (spMap (ChartBaseChange.jetCoeff V R (Fin d) m) ≫ x m)
  have hx'' := ChartBaseChange.isUnivChart_baseChange hπ hx hx'
  have hlaw : IsLawOf x' (FBMap.mapLaw (algebraMap V R) Gl).F := by
    refine ⟨fun i => ChartBaseChange.const_map (hGl.1 i), fun n a b y z hy hz => ?_⟩
    obtain ⟨Θ, t, hΘ, ht, e⟩ := ChartBaseChange.exists_move hπ hJ hx' ![a, b] ![y, z]
      (fun i => by fin_cases i; exacts [hy, hz])
    have H := hGl.2 2 _ _ _ _ (ht 0) (ht 1)
    have hFe : addOf Gl.F (pt V (n := 2) d 0) (pt V d 1) = Gl.F := funext fun i => ChartBaseChange.eval_standard_points_two _
    rw [hFe] at H
    refine (ChartBaseChange.rep_iff hπ hJ hx' (pair_points_zero_constant hy.1 hz.1) hΘ H _).2 fun m => ?_
    rw [ChartBaseChange.push_mul, MonObj.comp_mul, ← e 0 m, ← e 1 m]
    rfl
  have hser : ∀ i, IsSer1 x' (π ⁻¹ᵁ U) ((π.app U).hom (s i)) (MvPowerSeries.map (algebraMap V R) (S i)) := by
    intro i n a y hy
    obtain ⟨Θ, t, hΘ, ht, e⟩ := ChartBaseChange.exists_move hπ hJ hx' ![a] ![y] (fun i => by fin_cases i; exact hy)
    have H := hS i 1 _ _ (ht 0)
    rw [ChartBaseChange.germEval_oneStandardPoint_self] at H
    exact ChartBaseChange.hasSer_move hΘ π _ _ (fun m => congrArg (fun k => k.left) (e 0 m)) U _ _ H
  have hη : η[G'].left ≫ π = Spec.map (CommRingCat.ofHom (algebraMap V R)) ≫ η[G].left := by
    have e := congrArg (fun z => z.left) (map_one (pushHom hπ (𝟙_ _)))
    have e₁ : (1 : 𝟙_ _ ⟶ G') = η[G'] := by rw [Hom.one_def]; simp
    rw [e₁] at e
    refine e.trans ?_
    show (toUnit _ ≫ η[G]).left = _
    simp
  have hU' : ⊤ ≤ η[G'].left ⁻¹ᵁ (π ⁻¹ᵁ U) := by
    show ⊤ ≤ (η[G'].left ≫ π) ⁻¹ᵁ U
    rw [hη]
    exact top_le_preimage_comp _ _ U hU
  have val : ∀ (A : Type) [CommRing A] [Algebra R A] (r : sp (R₀ := R) A ⟶ G'), ⊤ ≤ r.left ⁻¹ᵁ (π ⁻¹ᵁ U) →
      fnVal r.left (π ⁻¹ᵁ U) (∑ i, resTop _ (scal G'.hom (c i)) * (π.app U).hom (s i)) =
        ∑ i, algebraMap R A (c i) * fnVal r.left (π ⁻¹ᵁ U) ((π.app U).hom (s i)) := by
    intro A _ _ r hr
    set_option synthInstance.maxHeartbeats 100000 in
      rw [fnVal_eq_fnValHom _ _ hr, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, ← fnVal_eq_fnValHom _ _ hr, ← fnVal_eq_fnValHom _ _ hr,
      fnVal_const r.left G'.hom (algebraMap R A) (Over.w r) _ hr]
  have hcomb : IsSer1 x' (π ⁻¹ᵁ U) (∑ i, resTop _ (scal G'.hom (c i)) * (π.app U).hom (s i))
      (∑ i, C (c i) * MvPowerSeries.map (algebraMap V R) (S i)) := by
    intro n a y hy m
    obtain ⟨τ, hτ, -⟩ := (hJ R (Fin n × Fin d)).1 m
    obtain ⟨Ψ, hΨ⟩ := exists_evHom (a := ![a]) (single_point_zero_constant hy.1)
    obtain ⟨hc, h0⟩ := (hRep R G' d x' hx'' (Fin n × Fin d)).2.2.1 a y hy
    have h₁ : ⊤ ≤ (y m).left ⁻¹ᵁ (π ⁻¹ᵁ U) := by
      refine top_le_preimage_of_nil (jetAug R (Fin n × Fin d) m).toRingHom
        (fun b => ⟨algebraMap R _ b, (jetAug R (Fin n × Fin d) m).commutes b⟩)
        (fun b hb => ⟨m + 1, ?_⟩) _ _ ?_
      · have : b ^ (m + 1) ∈ (RingHom.ker (jetAug R (Fin n × Fin d) m)) ^ (m + 1) := Ideal.pow_mem_pow hb _
        rwa [ker_jetAug_pow] at this
      · show ⊤ ≤ (spMap (jetAug R (Fin n × Fin d) m) ≫ y m).left ⁻¹ᵁ (π ⁻¹ᵁ U)
        rw [h0 m]
        exact top_le_preimage_comp (toUnit _ : sp (R₀ := R) R ⟶ _).left _ _ hU'
    refine ⟨h₁, (val _ (y m) h₁).trans ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hΨ, map_sum, ← hτ, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, ← hΨ (MvPowerSeries.map _ _), hτ (ev _ _), ← (hser i n a y hy m).2]
    congr 1
    exact ((congrArg τ (Ψ.commutes (c i))).trans (τ.commutes (c i))).symm
  refine EigenDer.dof_eq_of_eigen hJ hRep hSer R G' d x' hx'' (FBMap.mapLaw (algebraMap V R) Gl) hlaw _ hU' _ _ hcomb
    v y (dualLift v) (dualLift_zR v) fun A _ _ θ r h₁ h₂ => ?_
  letI : Algebra V A := ((algebraMap R A).comp (algebraMap V R)).toAlgebra
  haveI : IsScalarTower V R A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have e₀ : ((dualLift v).restrictScalars V).comp (ChartBaseChange.jetCoeff V R (Fin d) 1) = φ :=
    jet_ext fun j => by
      rw [hφ, AlgHom.comp_apply, ChartBaseChange.jetCoeff_zR]
      exact dualLift_zR v j
  have e₁ : ChartBaseChange.push hπ (r * (spMap θ ≫ spMap (dualLift v) ≫ x' 1)) =
      ChartBaseChange.push hπ r * (spMap (θ.restrictScalars V) ≫ spMap φ ≫ x 1) := by
    rw [ChartBaseChange.push_mul, ChartBaseChange.push_spMap, ChartBaseChange.push_spMap, hx', ← e₀]
    congr 2
    rw [← Category.assoc]
    congr 1
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, spMap_left]
    rw [← Spec.map_comp]
    rfl
  have := H A (θ.restrictScalars V) (ChartBaseChange.push hπ r) h₁ (by rw [← e₁]; exact h₂)
  rw [← e₁] at this
  rw [val _ _ h₁, val _ _ h₂]
  simp only [ChartBaseChange.fnVal_comp]
  have e₂ : ∀ i, (θ.restrictScalars V) (TrivSqZeroExt.inl (c i)) = algebraMap R A (c i) := fun i => θ.commutes (c i)
  simp only [e₂] at this
  exact this

end BaseChange

section Algebra

variable {d : ℕ} {𝒪 : Type} [CommRing 𝒪] [StarRing 𝒪]

theorem dof_ev_eq_zero {R : Type} [CommRing R] (B : FB R d 𝒪) (a : 𝒪) (u : Fin d → R)
    (hu : (dLin (B.A.act a)).mulVec u = 0) (g : PS R 1 d) : Dof B.G.F u (ev (n := 1) ![B.A.act a] g) = 0 := by
  have hom := B.A.hom a
  rw [FGLaw.add, FGLaw.add, QuadDeriv.addOf_pt] at hom
  rw [DerivEndo.dof_endo B.G.F B.G.const (congrFun (QuadDeriv.unit_right B.G)) (B.A.act a) (B.A.const a) hom, hu]
  obtain ⟨Ψ, hΨ⟩ := exists_evHom (a := ![B.A.act a]) (single_point_zero_constant (B.A.const a))
  have := DerivEndo.dof_smul_dir B.G.F 0 u g
  rw [zero_smul, map_zero, zero_mul] at this
  rw [this, hΨ, map_zero]

theorem dLin_map {R S : Type} [CommRing R] [CommRing S] (β : R →+* S) (φ : Pt R 1 d) :
    dLin (fun i => MvPowerSeries.map β (φ i) : Pt S 1 d) = (dLin φ).map β := by
  ext i j
  simp [dLin]

theorem coeff_dof_sub_mem {V O F : Type} [CommRing V] [CommRing O] [CommRing F] [Algebra ℚ F] [Algebra V F]
    (β : V →+* O) (io : O →+* F) (hio : Function.Injective io) (hβ : io.comp β = algebraMap V F) (I : Ideal O)
    (B : FB V d 𝒪) (a : 𝒪) (e : Fin d → O) (α yy : O) (hα : α ∈ I)
    (he : (dAct F B a).mulVec (fun i => io (e i)) = io α • fun i => io (e i)) (S : PS O 1 d)
    (hS : Dof (fun i => MvPowerSeries.map ((Ideal.Quotient.mk I).comp β) (B.G.F i))
        (fun i => Ideal.Quotient.mk I (e i)) (MvPowerSeries.map (Ideal.Quotient.mk I) S) =
      C (Ideal.Quotient.mk I yy) * MvPowerSeries.map (Ideal.Quotient.mk I) S)
    (r : PS V 1 d) (κ : V) (k : ℕ) (f : PS F 1 d)
    (hf : f = C (algebraMap V F κ) * MvPowerSeries.map io S *
      MvPowerSeries.map (algebraMap V F) (ev (n := 1) ![B.A.act a] r) ^ k) (mo) :
    ∃ x ∈ I, coeff mo (Dof (B.FK F) (fun i => io (e i)) f - C (io yy) * f) = io x := by
  let q := Ideal.Quotient.mk I
  let fO : PS O 1 d := C (β κ) * S * MvPowerSeries.map β (ev (n := 1) ![B.A.act a] r) ^ k
  have mm : ∀ {n : ℕ} {T : Type} [CommRing T] (ga : O →+* T) (g : PS V n d),
      MvPowerSeries.map ga (MvPowerSeries.map β g) = MvPowerSeries.map (ga.comp β) g := fun ga g => by
    ext m; simp
  have h₁ : f = MvPowerSeries.map io fO := by
    rw [hf, map_mul, map_mul, map_pow, mm, hβ, MvPowerSeries.map_C, ← hβ]; rfl
  have h₂ : Dof (B.FK F) (fun i => io (e i)) f - C (io yy) * f =
      MvPowerSeries.map io (Dof (fun i => MvPowerSeries.map β (B.G.F i)) e fO - C yy * fO) := by
    rw [map_sub, map_mul, InvDerMap.map_Dof, MvPowerSeries.map_C, ← h₁]
    simp only [mm, hβ]
    rfl
  refine ⟨coeff mo (Dof (fun i => MvPowerSeries.map β (B.G.F i)) e fO - C yy * fO), ?_, by rw [h₂, coeff_map]⟩
  have hO : ((dLin (B.A.act a)).map β).mulVec e = α • e := by
    funext i
    apply hio
    have := congrFun he i
    have e₁ : dAct F B a = ((dLin (B.A.act a)).map β).map io := by
      rw [Matrix.map_map, ← RingHom.coe_comp, hβ, ← dLin_map]; rfl
    rw [e₁] at this
    rw [RingHom.map_mulVec]
    exact this.trans (map_mul io _ _).symm
  have h₃ : Dof (fun i => MvPowerSeries.map (q.comp β) (B.G.F i)) (fun i => q (e i))
      (MvPowerSeries.map (q.comp β) (ev (n := 1) ![B.A.act a] r)) = 0 := by
    rw [FBMap.map_ev1 _ (B.A.const a)]
    refine dof_ev_eq_zero (FBMap.mapFB (q.comp β) B) a _ ?_ _
    show (dLin (fun i => MvPowerSeries.map (q.comp β) (B.A.act a i) : Pt (O ⧸ I) 1 d)).mulVec _ = 0
    rw [dLin_map]
    funext i
    have := congrArg q (congrFun hO i)
    rw [RingHom.map_mulVec, Matrix.map_map, Pi.smul_apply, smul_eq_mul, map_mul,
      Ideal.Quotient.eq_zero_iff_mem.2 hα, zero_mul] at this
    exact this
  have h₄ : ∀ n : ℕ, Dof (fun i => MvPowerSeries.map (q.comp β) (B.G.F i)) (fun i => q (e i))
      (MvPowerSeries.map (q.comp β) (ev (n := 1) ![B.A.act a] r) ^ n) = 0 := fun n => by
    induction n with
    | zero => rw [pow_zero, ← map_one (C : _ →+* PS (O ⧸ I) 1 d), GE.dof_C]
    | succ n ih => rw [pow_succ, GE.dof_mul, ih, h₃, mul_zero, mul_zero, add_zero]
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← coeff_map, map_sub, map_mul, InvDerMap.map_Dof, MvPowerSeries.map_C]
  simp only [fO, mm, map_mul, map_pow, MvPowerSeries.map_C]
  rw [GE.dof_mul, h₄, GE.dof_C_mul, hS]
  have : ∀ a b c e : PS (O ⧸ I) 1 d, a * b * 0 + c * (a * (e * b)) - e * (a * b * c) = 0 := fun a b c e => by ring
  rw [this, map_zero]

end Algebra

end GlobalTheory.EigenGerm
