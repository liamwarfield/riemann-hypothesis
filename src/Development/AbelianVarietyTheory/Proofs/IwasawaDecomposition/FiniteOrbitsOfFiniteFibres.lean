module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmDataIsCMExtAndGramIsHermND

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteOrbitsOfFiniteFibres
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

namespace GlobalTheory.Mem.Col2.StepOk

theorem finite_orbits_of_finite_fibres {G A B : Type} [Group G] [MulAction G A] [MulAction G B] (π : A → B)
    (hπ : ∀ (g : G) a, π (g • a) = g • π a) (hf : ∀ b, {a | π a = b}.Finite)
    [Finite (MulAction.orbitRel.Quotient G B)] : Finite (MulAction.orbitRel.Quotient G A) := by
  haveI : ∀ b, Finite {a | π a = b} := fun b => (hf b).to_subtype
  refine Finite.of_surjective (fun x : Σ q : MulAction.orbitRel.Quotient G B, {a | π a = q.out} =>
    (Quotient.mk _ x.2.1 : MulAction.orbitRel.Quotient G A)) ?_
  intro c
  induction c using Quotient.inductionOn' with
  | h a =>
    have h : (MulAction.orbitRel G B).r (Quotient.mk (MulAction.orbitRel G B) (π a)).out (π a) :=
      Quotient.exact (Quotient.out_eq _)
    obtain ⟨g, hg⟩ := h
    refine ⟨⟨Quotient.mk _ (π a), ⟨g • a, (hπ g a).trans hg⟩⟩, ?_⟩
    exact Quotient.sound ⟨g, rfl⟩

theorem ufGL_mulVec {E : Type} [Field E] [StarRing E] {n : ℕ} (γ : UF E n) (x : Fin n → E) :
    ((ufGL E n γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ x = γ.1 x :=
  LinearMap.toMatrix'_mulVec (γ.1 : Sp E n →ₗ[E] Sp E n) x

theorem ufGL_conjTranspose_mul {E : Type} [Field E] [StarRing E] {n : ℕ} (γ : UF E n) :
    ((ufGL E n γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)ᴴ *
      ((ufGL E n γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = 1 := by
  ext a b
  have h : ∑ i, star (γ.1 (Pi.single a 1) i) * γ.1 (Pi.single b 1) i =
      ∑ i, star ((Pi.single a 1 : Fin n → E) i) * (Pi.single b 1 : Fin n → E) i :=
    γ.2 (Pi.single a 1) (Pi.single b 1)
  have hv : ((ufGL E n γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
    LinearMap.toMatrix' (γ.1 : Sp E n →ₗ[E] Sp E n) := rfl
  rw [hv, Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe]
  refine Eq.trans ?_ (h.trans ?_)
  · rfl
  · rw [Finset.sum_eq_single a]
    · simp [Matrix.one_apply, Pi.single_apply]
    · intro c _ hc
      simp [Pi.single_apply, hc]
    · simp

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem levQ_root (Θ : LevQFam X.E X.K n Q) (h : ∀ P g, ∃ m : ℕ, 0 < m ∧ (Θ P).lam g ^ m = 1) (g : Θ.grp) :
    ∃ k : ℕ, 0 < k ∧ Θ.chr g ^ k = 1 := by
  rw [← isOfFinOrder_iff_pow_eq_one]
  unfold LevQFam.chr piChar
  erw [MonoidHom.finsetProd_apply]
  refine Finset.prod_induction _ IsOfFinOrder (fun _ _ ha hb => ha.mul hb) IsOfFinOrder.one fun P _ => ?_
  rw [isOfFinOrder_iff_pow_eq_one]
  exact h P _

theorem eq_one_of_fst (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (p : DecoF X.E n ST SG Q) (g : FrmG Λ Θ)
    (hg : FrmG.incl Λ Θ g • p = p) (h1 : g.1 = 1) : g = 1 := by
  have hb : FrmG.incl Λ Θ 1 • p = p := by rw [map_one, one_smul]
  have h2 := DecoSet.stab_fst_injective p.deco (a := ((FrmG.incl Λ Θ g).1, (FrmG.incl Λ Θ g).2.1))
    (b := ((FrmG.incl Λ Θ 1).1, (FrmG.incl Λ Θ 1).2.1)) (congrArg DecoF.deco hg) (congrArg DecoF.deco hb) h1
  exact FramedForms.incl_injective Λ Θ (FramedForms.stab_inj p hg hb h1 (Prod.mk.inj h2).2)

theorem stepY_ok : ∀ {X : Fields} {n : ℕ} {SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} (y : Ys X n) (β : Type) [Fintype β] [DecidableEq β] (Λ : β → LevFam X.E X.K n SG) (Θ : β → LevQFam X.E X.K n Q), X.Ok → ∀ (ST : Finset (HeightOneSpectrum (𝓞 X.E))) (pref : DecoF X.E n ST SG Q → Prop), (∀ b P, (Θ b P).H.FiniteIndex) → (∀ b P g, ∃ m : ℕ, 0 < m ∧ (Θ b P).lam g ^ m = 1) → (∀ N, Submodule.IsLattice X.E N → (y.ys N).Finite) → (stepY ST y β Λ Θ pref).Ok := by
  intro X n SG Q y β _ _ Λ Θ hX ST pref hfi hroot hfin
  have hG := fun b => FramedForms.main hX (ST := ST) (fun _ => ⟨fun _ => 0, fun _ _ _ => le_rfl⟩) (Λ b) (Θ b) (hfi b)
    (levQ_root (Θ b) (hroot b))
  refine ⟨fun b => ?_, fun b p => ?_, fun b g => ?_, fun b g => ?_, fun b g p x => ?_, fun b p => ?_, fun b g p hg h1 => ?_⟩
  · letI := ptYAct (ST := ST) y (Λ b) (Θ b)
    haveI : Finite (MulAction.orbitRel.Quotient (FrmG (Λ b) (Θ b)) (DecoF X.E n ST SG Q)) := (hG b).fin_orb
    refine finite_orbits_of_finite_fibres (G := FrmG (Λ b) (Θ b)) (A := PtY ST SG Q y) (B := DecoF X.E n ST SG Q)
      (fun p => p.1.1) (fun _ _ => rfl) fun d => ?_
    refine Set.Finite.of_finite_image (f := fun p : PtY ST SG Q y => p.1.2) ?_ ?_
    · refine (hfin d.deco.1.N d.deco.2.1).subset ?_
      rintro _ ⟨p, hp, rfl⟩
      have hp' : p.1.1 = d := hp
      rw [← hp']
      exact p.2
    · intro p hp q hq h
      exact Subtype.ext (Prod.ext (hp.trans hq.symm) h)
  · letI := ptYAct (ST := ST) y (Λ b) (Θ b)
    haveI : Finite (MulAction.stabilizer (FrmG (Λ b) (Θ b)) p.1.1) := (hG b).fin_stab p.1.1
    refine Finite.of_injective (fun a : MulAction.stabilizer (FrmG (Λ b) (Θ b)) (show PtY ST SG Q y from p) =>
      (⟨a.1, congrArg (fun q : PtY ST SG Q y => q.1.1) a.2⟩ : MulAction.stabilizer (FrmG (Λ b) (Θ b)) p.1.1)) ?_
    intro a c h
    have h' := congrArg Subtype.val h
    exact Subtype.ext h'
  · exact ufGL_conjTranspose_mul g.1
  · obtain ⟨m, hm, hc⟩ := FramedForms.chr_root (Λ b) (Θ b) (levQ_root (Θ b) (hroot b)) g
    exact ⟨m, hm, Units.ext ((Units.val_pow_eq_pow_val _ _).trans hc)⟩
  · have h := p.1.1.deco.1.Lsh_act g.1.2 g.2.1.1
    show ((ufGL X.E n g.1 : GL (Fin n) X.E) : Matrix (Fin n) (Fin n) X.E) *ᵥ x ∈ (p.1.1.deco.1.act g.1.1 g.2.1.1).Lsh ↔
      x ∈ p.1.1.deco.1.Lsh
    rw [h, ufGL_mulVec, mem_gmap, LinearEquiv.symm_apply_apply]
  · exact p.1.1.deco.2.Lsh_full_lattice
  · refine eq_one_of_fst (Λ b) (Θ b) p.1.1 g (congrArg (fun q : PtY ST SG Q y => q.1.1) hg) ?_
    have h2 : ufGL X.E n g.1 = 1 := h1
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    rw [← ufGL_mulVec, h2]
    simp

end GlobalTheory.Mem.Col2.StepOk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianLatticeChartFamilyLawBasis
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianLatticeChartFamilyLawBasis
noncomputable section

namespace GlobalTheory.Mem.Col2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms

section General

variable {K : Type} [Field K] (σ : K →+* ℂ) {V W C J : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]

theorem li_pi_of_basis [Finite C] [Fintype J] (e : Module.Basis J K V) (ev : V →ₛₗ[σ] W)
    (he : LinearIndependent ℂ fun j => ev (e j)) {κ : Type} (b : κ → C → V) (hb : LinearIndependent K b) :
    LinearIndependent ℂ fun i => fun c => ev (b i c) := by
  classical
  letI : Algebra K ℂ := σ.toAlgebra
  let r : (C → V) →ₗ[K] (C × J → K) :=
    LinearMap.pi fun p => (e.coord p.2) ∘ₗ LinearMap.proj p.1
  have hr : LinearMap.ker r = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro f hf
    funext c
    apply e.ext_elem
    intro j
    simpa [r] using congrFun hf (c, j)
  have h1 := (linearIndependent_algebraMap_comp_iff (S := ℂ)).2 (hb.map' r hr)
  let T : (C × J → ℂ) →ₗ[ℂ] (C → W) :=
    LinearMap.pi fun c => ∑ j, (LinearMap.proj (c, j) : (C × J → ℂ) →ₗ[ℂ] ℂ).smulRight (ev (e j))
  have hT : LinearMap.ker T = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro u hu
    funext p
    have h2 : ∑ j, u (p.1, j) • ev (e j) = 0 := by
      simpa [T, LinearMap.sum_apply] using congrFun hu p.1
    exact Fintype.linearIndependent_iff.1 he (fun j => u (p.1, j)) h2 p.2
  have h3 := h1.map' T hT
  suffices hs : (fun i => fun c => ev (b i c)) = T ∘ fun i => algebraMap K ℂ ∘ (r ∘ b) i by
    rw [hs]
    exact h3
  funext i c
  have h4 : b i c = ∑ j, e.repr (b i c) j • e j := (e.sum_repr _).symm
  conv_lhs => rw [h4]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.map_smulₛₗ]
  simp [T, r, LinearMap.sum_apply, RingHom.algebraMap_toAlgebra]

theorem mem_span_basis_image [Fintype J] (e : Module.Basis J K V) (ev : V →ₛₗ[σ] W) (x : V) :
    ev x ∈ Submodule.span ℂ (Set.range fun j => ev (e j)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← e.sum_repr x, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [LinearMap.map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem rho_sum_translates {G : Type} [Group G] [Fintype G] (ρ : G →* Module.End K V) (g : G) (x : V) :
    ρ g (∑ t, ρ t x) = ∑ t, ρ t x := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun t => ?_
  simp [map_mul]

end General

namespace GStep

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}
  (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n)


omit [StarRing E] [StarRing K] in
theorem evV_rho_eq_tr (b : S.β) (g : S.G b) (F : VV K lam) :
    evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ (S.rho emb lam b g F) =
      S.tr emb σ b g (evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ F) := by
  funext y
  have h1 : S.rho emb lam b g F = ((S.chr b g : Kˣ) : K) • rhoVr emb lam (S.gam b g) F := rfl
  rw [h1, LinearMap.map_smulₛₗ, tr, trFr_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  refine evV_rhoVr_tr emb _ lam σ _ F y _ ?_
  have h2 : y = frMul emb σ (S.gam b g) (frMul emb σ (S.gam b g)⁻¹ y) := by
    rw [← frMul_mul, mul_inv_cancel, frMul_one]
  intro τ
  exact congrFun (congrArg Subtype.val h2) τ

theorem lawBasis_of_ok (h : (S.fam emb lam).Ok) : S.LawBasis emb σ lam h := by
  classical
  haveI : Fintype S.Cl := h.fintypeCl
  constructor
  · have h1 : LinearIndependent K fun a => ((S.csd emb lam h).basis a).1 :=
      (S.csd emb lam h).basis.linearIndependent.map' (S.csd emb lam h).Forms.subtype (Submodule.ker_subtype _)
    exact li_pi_of_basis σ (C := S.Cl) (S.csd emb lam h).bV (evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ)
      (evV_linearIndependent emb _ lam σ (fr0 emb σ n) _ (S.csd emb lam h).bV.linearIndependent) _ h1
  · refine le_antisymm ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩ c
      refine ⟨evV_mem_ValC emb _ lam σ _, fun g => ?_⟩
      have h1 := ((S.csd emb lam h).basis a).2 c g
      have h2 := S.evV_rho_eq_tr emb σ lam c.1 g.1 (((S.csd emb lam h).basis a).1 c)
      exact h2.symm.trans (congrArg (evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ) h1)
    · intro φ hφ
      rw [← Finset.univ_sum_single φ]
      refine Submodule.sum_mem _ fun c _ => ?_
      letI : Fintype (S.Stab c) := (S.csd emb lam h).finGam c
      let A : (Fr emb σ n → ℂ) →ₗ[ℂ] (S.Cl → Fr emb σ n → ℂ) :=
        LinearMap.single ℂ (fun _ : S.Cl => Fr emb σ n → ℂ) c ∘ₗ ∑ g : S.Stab c, (S.tr emb σ c.1 g.1).toLinearMap
      have hA : ∀ w, A w = Pi.single c (∑ g : S.Stab c, S.tr emb σ c.1 g.1 w) := fun w => by
        simp [A, LinearMap.sum_apply]
      have hle : ValC (Gr emb σ n) lam ≤ (Submodule.span ℂ
          (Set.range fun a => S.embF emb σ lam h ((S.hlat emb lam h).b a))).comap A := by
        rw [← span_evV, Submodule.span_le]
        rintro _ ⟨F, rfl⟩
        let ρc : S.Stab c →* Module.End K (VV K lam) :=
          (S.rho emb lam c.1).comp (MulAction.stabilizer (S.G c.1) (S.rep c)).subtype
        let x : S.FormsK emb lam h := ⟨(Pi.single c (∑ t, ρc t F) : S.Cl → VV K lam), by
          intro c' γ
          by_cases hc : c' = c
          · subst hc
            show ρc γ ((Pi.single c' (∑ t, ρc t F) : S.Cl → VV K lam) c') =
              (Pi.single c' (∑ t, ρc t F) : S.Cl → VV K lam) c'
            rw [Pi.single_eq_same]
            exact rho_sum_translates ρc γ F
          · show S.rho emb lam c'.1 γ.1 ((Pi.single c (∑ t, ρc t F) : S.Cl → VV K lam) c') =
              (Pi.single c (∑ t, ρc t F) : S.Cl → VV K lam) c'
            rw [Pi.single_eq_of_ne hc, map_zero]⟩
        have hx : A (evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ F) = S.embF emb σ lam h x := by
          rw [hA]
          funext c'
          show _ = evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ ((Pi.single c (∑ t, ρc t F) : S.Cl → VV K lam) c')
          by_cases hc : c' = c
          · subst hc
            set_option synthInstance.maxHeartbeats 100000 in
              rw [Pi.single_eq_same, Pi.single_eq_same, map_sum]
            exact Finset.sum_congr rfl fun g _ => (S.evV_rho_eq_tr emb σ lam c'.1 g.1 F).symm
          · rw [Pi.single_eq_of_ne hc, Pi.single_eq_of_ne hc, map_zero]
        rw [SetLike.mem_coe, Submodule.mem_comap, hx]
        exact mem_span_basis_image σ (S.hlat emb lam h).b (S.embF emb σ lam h) x
      have h1 := Submodule.mem_comap.1 (hle (hφ c).1)
      have h2 : A (φ c) = (Fintype.card (S.Stab c) : ℂ) • (Pi.single c (φ c) : S.Cl → Fr emb σ n → ℂ) := by
        rw [hA, Finset.sum_congr rfl fun g _ => (hφ c).2 g, Finset.sum_const, Finset.card_univ, ← Pi.single_smul',
          Nat.cast_smul_eq_nsmul]
      rw [h2] at h1
      exact (Submodule.smul_mem_iff _ (Nat.cast_ne_zero.2 Fintype.card_ne_zero)).1 h1

end GStep

theorem lawBasis_all : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι]
    {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n),
    FOk emb σ → S.Ok → ∀ h, S.LawBasis emb σ lam h :=
  fun S emb σ lam _ _ h => S.lawBasis_of_ok emb σ lam h

end GlobalTheory.Mem.Col2
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianLatticeChartFamilyLawBasisStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianLatticeChartFamily_lawBasis : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n), FOk emb σ → S.Ok → ∀ h, S.LawBasis emb σ lam h := by
  first | exact @GlobalTheory.Mem.Col2.lawBasis_all | exact GlobalTheory.Mem.Col2.lawBasis_all | (intros; apply GlobalTheory.Mem.Col2.lawBasis_all <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexFormsFiniteDimensional
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexFormsFiniteDimensional
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.Col2

theorem valC_finiteDimensional {E K ι : Type} [Field E] [Field K] [CharZero K] [Fintype ι] {n : ℕ}
    (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n) :
    FiniteDimensional ℂ (ValC (Gr emb σ n) lam) := by
  classical
  have h := span_evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ
  have h2 : ValC (Gr emb σ n) lam ≤
      Submodule.span ℂ (Set.range fun i => evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ (bVV K lam i)) := by
    rw [← h, Submodule.span_le]
    rintro _ ⟨F, rfl⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← (bVV K lam).sum_repr F, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  haveI := FiniteDimensional.span_of_finite ℂ
    (Set.finite_range fun i => evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ (bVV K lam i))
  exact Submodule.finiteDimensional_of_le h2

theorem GStep.fi_finiteDimensional {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K]
    [StarRing K] [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n)
    (_hF : FOk emb σ) (hS : S.Ok) : FiniteDimensional ℂ (S.Fi emb σ lam) := by
  haveI := hS.fin_orb
  haveI := valC_finiteDimensional emb σ lam
  let f : S.Fi emb σ lam →ₗ[ℂ] (S.Cl → ValC (Gr emb σ n) lam) :=
    { toFun := fun φ c => ⟨φ.1 c, (φ.2 c).1⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective f fun a b hab => ?_
  apply Subtype.ext
  funext c
  exact congrArg Subtype.val (congrFun hab c)

end GlobalTheory.Mem.Col2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexFormsFiniteDimensionalStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexForms_finiteDimensional : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n), FOk emb σ → S.Ok → FiniteDimensional ℂ (S.Fi emb σ lam) := by
  first | exact @GlobalTheory.Mem.Col2.GStep.fi_finiteDimensional | exact GlobalTheory.Mem.Col2.GStep.fi_finiteDimensional | (intros; apply GlobalTheory.Mem.Col2.GStep.fi_finiteDimensional <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepAtZeroFree
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.Col2

theorem frm_free_zero {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (hX : X.Ok) (hPr : Pr.Ok)
    (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (u : Pr.Word) {Q : Finset (HeightOneSpectrum (𝓞 X.E))}
    (Λ : LevFam X.E X.K (R.N 0) Pr.vGs) (hΛ : Λ = colLev Ch 0) (Θ : LevQFam X.E X.K (R.N 0) Q) (g : FrmG Λ Θ)
    (p : DecoF X.E (R.N 0) (Pr.vT u) Pr.vGs Q) (hp : FrmG.incl Λ Θ g • p = p) : g = 1 := by
  subst hΛ
  have hpos : 0 < (Pr.vG 0).card := by
    rw [hPr.vG_card 0, Fields.f, hX.card_Tau]
    exact Module.finrank_pos
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
  have hw' : w ∈ Pr.vGs := by
    classical
    unfold Primes.vGs
    exact Finset.mem_union_left _ hw
  have hN : R.N 0 = R.k := by simp [Ranks.N]
  have hm : 0 < R.m := lt_of_lt_of_le (by norm_num) R.two_le_m
  have hmem : (g.2.1 : GLG (E := X.E) (n := R.N 0) (SG := Pr.vGs)) ⟨w, hw'⟩ ∈ (colLev Ch 0 ⟨w, hw'⟩).H :=
    (Subgroup.mem_pi _).mp g.2.1.2 ⟨w, hw'⟩ (Set.mem_univ _)
  rw [colLev_of_lt Ch hm] at hmem
  have ha : ((g.1, (g.2.1 : GLG (E := X.E) (n := R.N 0) (SG := Pr.vGs))) : UF X.E (R.N 0) × GLG (E := X.E) (n := R.N 0) (SG := Pr.vGs)) • p.deco = p.deco :=
    congrArg DecoF.deco hp
  have h1 : ((g.1, (g.2.1 : GLG (E := X.E) (n := R.N 0) (SG := Pr.vGs))) : UF X.E (R.N 0) × GLG (E := X.E) (n := R.N 0) (SG := Pr.vGs)) = 1 :=
    DecoSet.decoration_stabilizer_trivial_unipotent hX hPr p.deco ha 0 ⟨w, hw'⟩ hw (by rw [hN]; exact hbig)
      (isNilpotent_of_mem_HX_zero hN.le hmem)
  apply GlobalTheory.FramedForms.incl_injective
  rw [map_one]
  exact GlobalTheory.FramedForms.stab_inj p hp (one_smul _ p) (Prod.ext_iff.mp h1).1 (Prod.ext_iff.mp h1).2

theorem stepAt_zero_free {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
    (Tp : TopLev X Pr R (QE sel (mu : Chr X.F X.E X.K))) (u : Pr.Word) (hX : X.Ok) (hPr : Pr.Ok)
    (hbig : 2 * X.f * R.k < Pr.g 0 - 1) (hL : ∀ b, L.levG 0 b = colLev Ch 0) :
    (stepAt sel mu cst L Tp u 0).Free := by
  intro b g d hd
  have hm : 0 < R.m := lt_of_lt_of_le (by norm_num) R.two_le_m
  have hΛ : levGAt sel mu L Tp 0 b = colLev Ch 0 := by
    obtain ⟨b, hb⟩ := b
    obtain ⟨b0, rfl⟩ := Option.isSome_iff_exists.mp (hb.mpr hm)
    exact hL b0
  exact frm_free_zero Ch hX hPr hbig u _ hΛ _ g d.1.1 (congrArg (fun x => x.1.1) hd)

end GlobalTheory.Mem.Col2
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DerivAt0CompMem
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2.JetEx
open scoped ContDiff

namespace GlobalTheory.Mem.JetChain

variable {ι : Type} [Fintype ι] {a b : ℕ}

theorem eq_sum_coordX (z : VCx ι a b) : z = ∑ k : DVar ι a b, z k.1 k.2.1 k.2.2 • coordX k := by
  classical
  funext τ i j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single (τ, i, j)]
  · simp [coordX]
  · rintro ⟨τ', i', j'⟩ _ h
    have : ¬ (τ = τ' ∧ i = i' ∧ j = j') := by
      rintro ⟨rfl, rfl, rfl⟩
      exact h rfl
    simp [coordX, this]
  · simp

theorem exists_derivAt0 (G : VCx ι a b → ℂ) (hG : ∀ k : ℕ, ContDiff ℂ k G) {n : ℕ} (f : Fin n → DVar ι a b) :
    ∃ e : DVar ι a b →₀ ℕ, e.degree = n ∧ iteratedFDeriv ℂ n G 0 (fun i => coordX (f i)) = derivAt0 G e := by
  classical
  have hG' : ContDiff ℂ ∞ G := contDiff_infty.2 hG
  set e : DVar ι a b →₀ ℕ := Multiset.toFinsupp (↑(List.ofFn f) : Multiset (DVar ι a b)) with he
  have hm : Finsupp.toMultiset e = (↑(List.ofFn f) : Multiset (DVar ι a b)) := by
    rw [he, Multiset.toFinsupp_toMultiset]
  have hc : (Finsupp.toMultiset e).card = n := by rw [hm]; simp
  refine ⟨e, ?_, ?_⟩
  · rw [← hc, Finsupp.card_toMultiset]; rfl
  have p : ((List.ofFn f).map coordX).Perm ((Finsupp.toMultiset e).toList.map coordX) := by
    refine List.Perm.map _ ?_
    rw [← Multiset.coe_eq_coe, Multiset.coe_toList, hm]
  have h2 := ReciprocityTheory.ChartRestriction.G.PullbackSections.cml_perm p n (iteratedFDeriv ℂ _ G 0)
    (fun v σ => ReciprocityTheory.L2DbarEstimates.Y.zd_iteratedFDeriv_comp_perm isOpen_univ hG'.contDiffOn _ 0 trivial σ v)
    (by simp) (by simp [hc])
  have h3 : ∀ (n n' : ℕ) (h : n = n') (v : Fin n → VCx ι a b) (w : Fin n' → VCx ι a b), (∀ i, v i = w (i.cast h)) →
      iteratedFDeriv ℂ n G 0 v = iteratedFDeriv ℂ n' G 0 w := by
    intro n n' h v w hvw
    subst h
    exact congrArg _ (funext hvw)
  unfold derivAt0
  refine Eq.trans (congrArg _ (funext fun i => ?_)) (h2.trans (h3 _ _ hc.symm _ _ fun i => ?_))
  · simp
  · simp

theorem derivAt0_comp_mem : ∀ (ι : Type) [Fintype ι] (a b n : ℕ) (K₀ : Subfield ℂ) (G : VCx ι a b → ℂ) (L : VCx ι a b →ₗ[ℂ] VCx ι a b) (κ : ℂ), (∀ k : ℕ, ContDiff ℂ k G) → (∀ k τ i j, L (coordX k) τ i j ∈ K₀) → (∀ e : DVar ι a b →₀ ℕ, e.degree = n → κ * derivAt0 G e ∈ K₀) → ∀ e : DVar ι a b →₀ ℕ, e.degree = n → κ * derivAt0 (fun z => G (L z)) e ∈ K₀ := by
  intro ι _ a b n K₀ G L κ hG hL hK e he
  classical
  have hc : (Finsupp.toMultiset e).card = n := by
    rw [← he, Finsupp.card_toMultiset]; rfl
  subst hc
  let T : VCx ι a b →L[ℂ] VCx ι a b := LinearMap.toContinuousLinearMap L
  have h1 : (fun z => G (L z)) = G ∘ T := rfl
  have key : ∀ g : Fin (Finsupp.toMultiset e).card → DVar ι a b,
      κ * iteratedFDeriv ℂ _ G 0 (fun i => L (coordX (g i))) ∈ K₀ := by
    intro g
    have h2 : (fun i => L (coordX (g i))) =
        fun i => ∑ k : DVar ι a b, L (coordX (g i)) k.1 k.2.1 k.2.2 • coordX k :=
      funext fun i => eq_sum_coordX _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h2, ContinuousMultilinearMap.map_sum, Finset.mul_sum]
    refine sum_mem fun f _ => ?_
    rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul, mul_left_comm]
    refine mul_mem (prod_mem fun i _ => hL _ _ _ _) ?_
    obtain ⟨e', he', h⟩ := exists_derivAt0 G hG f
    rw [h]
    exact hK e' he'
  unfold derivAt0
  rw [h1, T.iteratedFDeriv_comp_right (hG _) 0 le_rfl, map_zero, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  exact key _

end GlobalTheory.Mem.JetChain
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianLatticeChartFamilyFamOk
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianLatticeChartFamilyFamOk
noncomputable section

namespace GlobalTheory.Mem.Col2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Matrix

section

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}


omit [NumberField K] [StarRing K] in
theorem GStep.lsh_eq_map (S : GStep E K n) (h : S.Ok) (b : S.β) (g : S.G b) (d : S.D b) :
    S.Lsh b (g • d) = (S.Lsh b d).map
      ((Matrix.mulVecLin (S.gam b g : Matrix (Fin n) (Fin n) E)).restrictScalars (𝓞 E)) := by
  ext y
  simp only [Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply]
  have e : (S.gam b g : Matrix (Fin n) (Fin n) E) *ᵥ (((S.gam b g)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ y = y := by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  constructor
  · intro hy
    exact ⟨_, (h.lsh_smul b g d _).1 (by rw [e]; exact hy), e⟩
  · rintro ⟨x, hx, rfl⟩
    exact (h.lsh_smul b g d x).2 hx


omit [StarRing K] [Fintype ι] in
theorem GStep.tauLat_smul (S : GStep E K n) (h : S.Ok) (emb : ι → E →+* K) [Fintype ι] (b : S.β) (g : S.G b) (d : S.D b) (τ : ι) :
    tauLat emb τ (S.Lsh b (g • d)) = gLat (embGL emb (S.gam b g) τ) (tauLat emb τ (S.Lsh b d)) := by
  rw [S.lsh_eq_map h]
  exact tauLatG E K ι n emb τ _ (S.gam b g)

end

theorem fam_ok : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι]
    {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n),
    FOk emb σ → S.Ok → (S.fam emb lam).Ok := by
  intro E K ι _ _ _ _ _ _ _ n S emb σ lam hF h b
  have hr : ∀ g : S.G b, ∃ m : ℕ, 0 < m ∧ ((S.chr b g : Kˣ) : K) ^ m = 1 := fun g => by
    obtain ⟨m, hm, hc⟩ := h.root b g
    exact ⟨m, hm, by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]⟩
  refine ⟨h.fin_orb b, h.fin_stab b, ?_, ?_, ?_⟩
  · intro g d
    obtain ⟨m, hm, hc⟩ := hr g
    refine Eq.trans ?_ (map_root_smul _ (rhoVr emb lam (S.gam b g)) hm hc).symm
    show nabAtr emb lam (S.Lsh b (g • d)) = (nabAtr emb lam (S.Lsh b d)).map _
    unfold nabAtr
    simp_rw [S.tauLat_smul h emb b g d, dualFr_gLat]
    exact nabK_gLat lam _ (invTrK (embGL emb (S.gam b g)))
  · intro g d
    obtain ⟨m, hm, hc⟩ := hr g
    refine Eq.trans ?_ (map_root_smul _ (rhoVr emb lam (S.gam b g)) hm hc).symm
    show delAtr emb lam (S.Lsh b (g • d)) = (delAtr emb lam (S.Lsh b d)).map _
    unfold delAtr
    simp_rw [S.tauLat_smul h emb b g d, dualFr_gLat]
    exact delK_gLat lam _ (invTrK (embGL emb (S.gam b g)))
  · intro g x y
    obtain ⟨m, hm, hc⟩ := hr g
    have hU : S.gam b g ∈ Formalism.UG.UJ (starRingEnd E) (1 : Matrix (Fin n) (Fin n) E) := by
      have := h.unit b g
      show _ * _ * _ = _
      rw [Matrix.mul_one]
      exact this
    have hi : pairVr emb lam (1 : Matrix (Fin n) (Fin n) E) (rhoVr emb lam (S.gam b g) x) (rhoVr emb lam (S.gam b g) y) =
        pairVr emb lam (1 : Matrix (Fin n) (Fin n) E) x y :=
      pairInv K ι n lam _ _ (fun τ => (uJUnitary E K ι n emb (starRingEnd E) τ
        (fun x => (hF.emb_star τ x).symm) 1 _ hU).2 (by simp)) x y
    show pairVr emb lam (1 : Matrix (Fin n) (Fin n) E) (((S.chr b g : Kˣ) : K) • rhoVr emb lam (S.gam b g) x)
      (((S.chr b g : Kˣ) : K) • rhoVr emb lam (S.gam b g) y) = pairVr emb lam (1 : Matrix (Fin n) (Fin n) E) x y
    rw [LinearMap.map_smulₛₗ₂, map_smul, hi, smul_smul]
    show (star ((S.chr b g : Kˣ) : K) * _) • _ = _
    rw [star_mul_root ⟨σ, hF.sig_star⟩ hm hc, one_smul]

end GlobalTheory.Mem.Col2

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianLatticeChartFamilyFamOkStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianLatticeChartFamily_fam_ok : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n), FOk emb σ → S.Ok → (S.fam emb lam).Ok := by
  first | exact @GlobalTheory.Mem.Col2.fam_ok | exact GlobalTheory.Mem.Col2.fam_ok | (intros; apply GlobalTheory.Mem.Col2.fam_ok <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFunctionalDilatedClass
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFunctionalDilatedClass
noncomputable section

namespace GlobalTheory.Mem.Col2.DilFv

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

theorem exists_red_equiv {R M M' : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (I : Ideal R) (u : M ≃ₗ[R] M') :
    ∃ e : (M ⧸ (I • (⊤ : Submodule R M))) ≃ₗ[R ⧸ I] (M' ⧸ (I • (⊤ : Submodule R M'))),
      ∀ x, e (Submodule.Quotient.mk x) = Submodule.Quotient.mk (u x) := by
  have h : (I • (⊤ : Submodule R M)).map (u : M →ₗ[R] M') = I • (⊤ : Submodule R M') := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
  refine ⟨(Submodule.Quotient.equiv _ _ u h).extendScalarsOfSurjective Ideal.Quotient.mk_surjective, fun x => rfl⟩

theorem exists_red_dual {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R) (u : M →ₗ[R] R ⧸ I) :
    ∃ φ : (M ⧸ (I • (⊤ : Submodule R M))) →ₗ[R ⧸ I] (R ⧸ I), ∀ x, φ (Submodule.Quotient.mk x) = u x := by
  have h : (I • (⊤ : Submodule R M)) ≤ LinearMap.ker u := by
    refine Submodule.smul_le.2 fun r hr x _ => ?_
    rw [LinearMap.mem_ker, map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.2 hr, zero_mul]
  exact ⟨(Submodule.liftQ _ u h).extendScalarsOfSurjective Ideal.Quotient.mk_surjective, fun x => rfl⟩

variable {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {S : GStep E K n}
  {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) {T : ℕ}

theorem fv_mk (h : A.Ok T) (P : ST) (c : S.Cl) (x : A.N c.1 (S.rep c)) :
    A.fv P c (Submodule.Quotient.mk x) = A.f c.1 (S.rep c) P x := by
  have hex : ∃ φ : Module.Dual (Res P.1) (A.lv P c), ∀ x : A.N c.1 (S.rep c),
      φ (Submodule.Quotient.mk x) = A.f c.1 (S.rep c) P x :=
    exists_red_dual P.1.asIdeal
      { toFun := fun x : A.N c.1 (S.rep c) => A.f c.1 (S.rep c) P x
        map_add' := fun x y => h.f_add _ _ P x x.2 y y.2
        map_smul' := fun a x => h.f_smul _ _ P a x x.2 }
  unfold TDat.fv
  rw [dite_eq_left hex]
  exact hex.choose_spec x

theorem exists_act_equiv (h : A.Ok T) (b : S.β) (g : S.G b) (d : S.D b) (M : Submodule (𝓞 E) (Fin n → E))
    (hM : A.N b (g • d) = M) :
    ∃ u : A.N b d ≃ₗ[𝓞 E] M, ∀ x, (u x : Fin n → E) = (S.gam b g : Matrix (Fin n) (Fin n) E) *ᵥ (x : Fin n → E) := by
  subst hM
  have h1 : ∀ x : Fin n → E, (S.gam b g : Matrix (Fin n) (Fin n) E) *ᵥ
      ((S.gam b g⁻¹ : Matrix (Fin n) (Fin n) E) *ᵥ x) = x := fun x => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mulVec]
  have h2 : ∀ x : Fin n → E, (S.gam b g⁻¹ : Matrix (Fin n) (Fin n) E) *ᵥ
      ((S.gam b g : Matrix (Fin n) (Fin n) E) *ᵥ x) = x := fun x => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mulVec]
  refine ⟨{ toFun := fun x => ⟨(S.gam b g : Matrix (Fin n) (Fin n) E) *ᵥ x.1, (h.N_act b g d x.1).2 x.2⟩
            invFun := fun y => ⟨(S.gam b g⁻¹ : Matrix (Fin n) (Fin n) E) *ᵥ y.1,
              (h.N_act b g d _).1 (by rw [h1]; exact y.2)⟩
            map_add' := fun x y => Subtype.ext (Matrix.mulVec_add _ x.1 y.1)
            map_smul' := fun a x => Subtype.ext (Matrix.mulVec_smul _ a x.1)
            left_inv := fun x => Subtype.ext (h2 _)
            right_inv := fun y => Subtype.ext (h1 _) }, fun x => rfl⟩

theorem dil_fv : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S : GStep E K n}
    {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) (T : ℕ), S.Ok → A.Ok T → ∀ P a c,
    ∃ e : A.lv P (S.cl c.1 (A.diaPt P a c)) ≃ₗ[Res P.1] A.lv P c,
      ∀ x, A.fv P (S.cl c.1 (A.diaPt P a c)) x = (a : Res P.1) * A.fv P c (e x) := by
  intro E K _ _ _ _ n S ST A T _ h P a c
  obtain ⟨g, hmv⟩ : ∃ g : S.G c.1, g • S.rep (S.cl c.1 (A.diaPt P a c)) = A.diaPt P a c :=
    (MulAction.orbitRel (S.G c.1) (S.D c.1)).symm (Quotient.exact (S.rp_spec c.1 (Quotient.mk _ (A.diaPt P a c))))
  obtain ⟨u, hu⟩ := exists_act_equiv A h c.1 g (S.rep (S.cl c.1 (A.diaPt P a c)))
    (A.N c.1 (S.rep c)) (by rw [hmv]; exact h.dia_N _ _ _ _)
  obtain ⟨e, he⟩ := exists_red_equiv P.1.asIdeal u
  refine ⟨e, fun x => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have e1 := fv_mk A h P (S.cl c.1 (A.diaPt P a c)) x
  have e2 := fv_mk A h P c (u x)
  have e3 := h.f_act c.1 g (S.rep (S.cl c.1 (A.diaPt P a c))) P x
  rw [hmv, ← hu] at e3
  have e4 := h.dia_f c.1 P a (S.rep c) (u x)
  refine e1.trans (e3.symm.trans (e4.trans ?_))
  exact congrArg _ (e2.symm.trans (congrArg _ (he x).symm))

end GlobalTheory.Mem.Col2.DilFv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFunctionalDilatedClassStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelFunctional_dilated_class : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S : GStep E K n} {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) (T : ℕ), S.Ok → A.Ok T → ∀ P a c, ∃ e : A.lv P (S.cl c.1 (A.diaPt P a c)) ≃ₗ[Res P.1] A.lv P c, ∀ x, A.fv P (S.cl c.1 (A.diaPt P a c)) x = (a : Res P.1) * A.fv P c (e x) := by
  first | exact @GlobalTheory.Mem.Col2.DilFv.dil_fv | exact GlobalTheory.Mem.Col2.DilFv.dil_fv | (intros; apply GlobalTheory.Mem.Col2.DilFv.dil_fv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.YsAtFiniteNonempty
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

open Formalism.HermitianLatticesTheory (localization₂)

namespace GlobalTheory.Mem.CosetFin

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}


omit [StarRing E] in
theorem exists_reps (N : Submodule (𝓞 E) (Sp E n)) (hN : N.FG) (m : ℕ) (hm : m ≠ 0) :
    ∃ T : Set (Sp E n), T.Finite ∧ ∀ x ∈ N, ∃ t ∈ T, ∃ z ∈ N, x - t = (m : 𝓞 E) • z := by
  haveI : Module.Finite (𝓞 E) N := Module.Finite.iff_fg.2 hN
  haveI : Module.Finite ℤ N := Module.Finite.trans (𝓞 E) N
  let M : Submodule ℤ N := LinearMap.range (LinearMap.lsmul ℤ N (m : ℤ))
  haveI : Finite (N ⧸ M) := by
    refine Module.finite_of_fg_torsion _ fun x => ⟨⟨(m : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hm)⟩, ?_⟩
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective M x
    show (m : ℤ) • (Submodule.Quotient.mk y : N ⧸ M) = 0
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ⟨y, rfl⟩
  refine ⟨Set.range fun q : N ⧸ M => ((Quotient.out q : N) : Sp E n), Set.finite_range _, fun x hx => ?_⟩
  refine ⟨_, ⟨Submodule.Quotient.mk ⟨x, hx⟩, rfl⟩, ?_⟩
  have h : (⟨x, hx⟩ : N) - Quotient.out (Submodule.Quotient.mk (p := M) ⟨x, hx⟩) ∈ M :=
    (Submodule.Quotient.eq M).1 (Quotient.out_eq _).symm
  obtain ⟨z, hz⟩ := h
  refine ⟨z, z.2, ?_⟩
  have h2 := congrArg Subtype.val hz
  simp only [LinearMap.lsmul_apply, AddSubgroupClass.coe_sub, natCast_zsmul] at h2
  rw [← h2, Nat.cast_smul_eq_nsmul]
  rfl

theorem exists_reps_loc (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n)) (hN : N.FG) (m : ℕ) (hm : m ≠ 0) :
    ∃ T : Set (Sp E n), T.Finite ∧
      ∀ x ∈ localization₂ P.asIdeal N, ∃ t ∈ T, ((m : E)⁻¹) • (x - t) ∈ localization₂ P.asIdeal N := by
  obtain ⟨T, hT, h⟩ := exists_reps N hN m hm
  refine ⟨T, hT, fun x hx => ?_⟩
  obtain ⟨s, hs, hsx⟩ := (mem_locP P N x).1 hx
  have hk : ∀ k : ℕ, s ^ (k + 1) • x ∈ N := fun k => by
    rw [pow_succ, mul_smul]; exact N.smul_mem _ hsx
  choose t ht z hz he using fun k => h _ (hk k)
  haveI := hT.to_subtype
  obtain ⟨i, j, hij, hEq⟩ : ∃ i j : ℕ, i < j ∧ t i = t j := by
    obtain ⟨a, b, hab, h1⟩ := Finite.exists_ne_map_eq_of_infinite (fun k => (⟨t k, ht k⟩ : T))
    have h1' : t a = t b := congrArg Subtype.val h1
    rcases lt_or_gt_of_ne hab with h2 | h2
    · exact ⟨a, b, h2, h1'⟩
    · exact ⟨b, a, h2, h1'.symm⟩
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_lt hij
  refine ⟨t p, ht p, (mem_locP P N _).2 ⟨s ^ (i + 1), fun hh => hs (P.isPrime.mem_of_pow_mem _ hh), ?_⟩⟩
  have hm' : (m : E) ≠ 0 := by exact_mod_cast hm
  have e1 : s ^ (i + 1) • (x - t p) = (m : 𝓞 E) • (z i - z (i + p + 1) + s ^ (i + 1) • z p) := by
    rw [smul_add, smul_sub (m : 𝓞 E), ← he i, ← he (i + p + 1), smul_comm (m : 𝓞 E), ← he p, hEq, smul_sub, smul_sub,
      ← mul_smul, ← pow_add, show i + 1 + (p + 1) = i + p + 1 + 1 by ring]
    abel
  rw [smul_comm, e1, Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E, inv_smul_smul₀ hm']
  exact N.add_mem (N.sub_mem (hz _) (hz _)) (N.smul_mem _ (hz _))

theorem exists_reps_pow (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n)) (hN : N.FG) (a b : ℤ) :
    ∃ T : Set (Sp E n), T.Finite ∧ ∀ x : Sp E n, ((qOf P : E) ^ a)⁻¹ • x ∈ localization₂ P.asIdeal N →
      ∃ t ∈ T, ((qOf P : E) ^ b)⁻¹ • (x - t) ∈ localization₂ P.asIdeal N := by
  have hq : qOf P ≠ 0 := fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hq' : (qOf P : E) ≠ 0 := by exact_mod_cast hq
  obtain ⟨T, hT, h⟩ := exists_reps_loc P N hN (qOf P ^ (b - a).toNat) (pow_ne_zero _ hq)
  refine ⟨(fun t => (qOf P : E) ^ a • t) '' T, hT.image _, fun x hx => ?_⟩
  obtain ⟨t, ht, h1⟩ := h _ hx
  refine ⟨_, ⟨t, ht, rfl⟩, ?_⟩
  have h2 := (localization₂ P.asIdeal N).smul_mem ((qOf P ^ (a - b).toNat : ℕ) : 𝓞 E) h1
  rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E] at h2
  have e : ((qOf P ^ (a - b).toNat : ℕ) : E) * ((qOf P ^ (b - a).toNat : ℕ) : E)⁻¹ = ((qOf P : E) ^ b)⁻¹ * (qOf P : E) ^ a := by
    push_cast
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_neg, ← zpow_add₀ hq', ← zpow_add₀ hq']
    congr 1
    omega
  rw [smul_smul, e, mul_smul, smul_sub, smul_inv_smul₀ (zpow_ne_zero _ hq')] at h2
  exact h2

theorem finite_cosets (SB : Finset (HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Sp E n)) (hN : N.FG) (a b : SB → ℤ) :
    {Y : Set (Sp E n) | ∃ y ∈ locLat SB N a, Y = {z | z - y ∈ locLat SB N b}}.Finite := by
  choose T hT h using fun P : SB => exists_reps_pow P.1 N hN (a P) (b P)
  refine ((Set.Finite.pi' hT).image fun t : SB → Sp E n =>
    {z | ∀ P : SB, ((qOf P.1 : E) ^ b P)⁻¹ • (z - t P) ∈ localization₂ P.1.asIdeal N}).subset ?_
  rintro Y ⟨y, hy, rfl⟩
  choose t ht h1 using fun P => h P y ((mem_locLat SB N a y).1 hy P)
  refine ⟨t, ht, ?_⟩
  ext z
  simp only [Set.mem_setOf_eq, mem_locLat]
  refine forall_congr' fun P => ?_
  have e : z - t P = (z - y) + (y - t P) := by abel
  rw [e, smul_add]
  exact (localization₂ P.1.asIdeal N).add_mem_iff_left (h1 P)

theorem ysAt_finite_nonempty : ∀ {X : Fields} {Pr : Primes X} (R : Ranks)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (j : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E (R.N j))), Submodule.IsLattice X.E N →
      ((ysAt R sel mu cst j).ys N).Finite ∧ ((ysAt R sel mu cst j).ys N).Nonempty := by
  intro X Pr R sel S mu cst j N hN
  unfold ysAt
  split_ifs
  · exact ⟨finite_cosets _ N hN.fg _ _, _, 0, zero_mem _, rfl⟩
  · exact ⟨Set.finite_singleton _, Set.singleton_nonempty _⟩

end GlobalTheory.Mem.CosetFin
end
