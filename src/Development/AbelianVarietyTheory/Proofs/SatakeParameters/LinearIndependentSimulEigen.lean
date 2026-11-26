module

public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AutFormDefiniteUnitaryEqSumPolynomialMulAutForm
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AutFormDefiniteUnitaryEqSumPolynomialMulAutFormStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsConjIsAutFormU
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsDefiniteUnitaryFunctionPolynomialMulSmooth
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsDefiniteUnitaryFunctionPolynomialMulSmooth
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.UnitaryBC

theorem continuous_of_right_invariant_open {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (e : G → ℂ) (V : Subgroup G) (hV : IsOpen (V : Set G)) (h : ∀ u ∈ V, ∀ g, e (g * u) = e g) :
    Continuous e := by
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open e).2 fun x => ?_)
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (V : Set G), hV.preimage (by fun_prop), by simp, fun y hy => ?_⟩
  rw [← h _ hy x, mul_inv_cancel_left]

theorem exists_fun_of_poly_smooth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (m : ℕ) (p : Fin m → infU E n → ℂ) (e : Fin m → finU (E := E) (n := n) → ℂ), (∀ i, p i ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}) → (∀ i, ∃ V : Subgroup (finU (E := E) (n := n)), IsOpen (V : Set (finU (E := E) (n := n))) ∧ ∀ u ∈ V, ∀ g, e i (g * u) = e i g) → ∃ φ : UA E n → ℂ, Continuous φ ∧ IsOpen {k : finU (E := E) (n := n) | RU E n k φ = φ} ∧ FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : infU E n => RU E n k φ)) ∧ ∀ (g : finU (E := E) (n := n)) (k : infU E n), φ (g.1 * k.1) = ∑ i, p i k * e i g := by
  intro E _ _ _ n m p e hp he
  obtain ⟨-, -, -, a, b, ha, hb, -, hab⟩ := GlobalTheory.T.definiteUnitary_realApprox_and_finite_infinite_split E n
  obtain ⟨hcont, -, -, -, hco⟩ := GlobalTheory.T.unitary_coordinate_algebra_dense E n
  choose V hVo hV using he
  have haf : ∀ g : finU (E := E) (n := n), a g.1 = g := fun g => by simpa using (hab g 1).1
  have hbf : ∀ g : finU (E := E) (n := n), b g.1 = 1 := fun g => by simpa using (hab g 1).2
  have hai : ∀ k : infU E n, a k.1 = 1 := fun k => by simpa using (hab 1 k).1
  have hbi : ∀ k : infU E n, b k.1 = k := fun k => by simpa using (hab 1 k).2
  have hR : ∀ (x : UA E n) (φ : UA E n → ℂ) (g : UA E n), RU E n x φ g = φ (g * x) := fun _ _ _ => rfl
  refine ⟨fun x => ∑ i, p i (b x) * e i (a x), ?_, ?_, ?_, fun g k => ?_⟩
  · exact continuous_finsetSum _ fun i _ => ((hcont _ (hp i)).comp hb).mul
      ((continuous_of_right_invariant_open _ _ (hVo i) (hV i)).comp ha)
  · set φ : UA E n → ℂ := fun x => ∑ i, p i (b x) * e i (a x) with hφ
    let S : Subgroup (finU (E := E) (n := n)) :=
      { carrier := {k : finU (E := E) (n := n) | RU E n k φ = φ}
        one_mem' := by
          change RU E n ((1 : finU (E := E) (n := n)) : UA E n) φ = φ
          funext g
          rw [hR]
          simp
        mul_mem' := fun {x y} hx hy => by
          change RU E n ((x * y : finU (E := E) (n := n)) : UA E n) φ = φ
          funext g
          have h1 := congrFun (show RU E n x φ = φ from hx) g
          have h2 := congrFun (show RU E n y φ = φ from hy) (g * x)
          rw [hR] at h1 h2 ⊢
          rw [Subgroup.coe_mul, ← mul_assoc, h2, h1]
        inv_mem' := fun {x} hx => by
          change RU E n ((x⁻¹ : finU (E := E) (n := n)) : UA E n) φ = φ
          funext g
          have h1 := congrFun (show RU E n x φ = φ from hx) (g * (x : UA E n)⁻¹)
          rw [hR] at h1 ⊢
          rw [Subgroup.coe_inv, ← h1, inv_mul_cancel_right] }
    have hle : (⨅ i, V i) ≤ S := fun u hu => by
      change RU E n (u : UA E n) φ = φ
      funext g
      rw [hR]
      simp only [hφ, map_mul, haf, hbf, mul_one]
      exact Finset.sum_congr rfl fun i _ => by rw [hV i u (Subgroup.mem_iInf.1 hu i)]
    refine Subgroup.isOpen_mono hle ?_
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite hVo
  · choose N c d _ hcd using fun i => hco _ (hp i)
    let f : (Σ i, Fin (N i)) → UA E n → ℂ := fun s x => c s.1 s.2 (b x) * e s.1 (a x)
    haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range f)) :=
      FiniteDimensional.span_of_finite ℂ (Set.finite_range f)
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range f)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    have : RU E n k (fun x => ∑ i, p i (b x) * e i (a x)) = ∑ s : Σ i, Fin (N i), d s.1 s.2 k • f s := by
      funext g
      rw [hR]
      simp only [map_mul, hai, hbi, mul_one, hcd, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, f,
        Fintype.sum_sigma, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    change RU E n k _ ∈ _
    rw [this]
    exact Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)
  · simp only [(hab g k).1, (hab g k).2]

end GlobalTheory.UnitaryBC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsDefiniteUnitaryFunctionPolynomialMulSmoothStatement
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_definiteUnitary_function_polynomial_mul_smooth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (m : ℕ) (p : Fin m → infU E n → ℂ) (e : Fin m → finU (E := E) (n := n) → ℂ), (∀ i, p i ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}) → (∀ i, ∃ V : Subgroup (finU (E := E) (n := n)), IsOpen (V : Set (finU (E := E) (n := n))) ∧ ∀ u ∈ V, ∀ g, e i (g * u) = e i g) → ∃ φ : UA E n → ℂ, Continuous φ ∧ IsOpen {k : finU (E := E) (n := n) | RU E n k φ = φ} ∧ FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : infU E n => RU E n k φ)) ∧ ∀ (g : finU (E := E) (n := n)) (k : infU E n), φ (g.1 * k.1) = ∑ i, p i k * e i g := by
  first | exact @GlobalTheory.UnitaryBC.exists_fun_of_poly_smooth | exact GlobalTheory.UnitaryBC.exists_fun_of_poly_smooth | (intros; apply GlobalTheory.UnitaryBC.exists_fun_of_poly_smooth <;> assumption)
end
end

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.UnitaryBC

theorem exists_conj_isAutFormU (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (σ : ℂ ≃+* ℂ)
    (φ : UA E n → ℂ) (hφ : IsAutFormU φ) :
    ∃ φ' : UA E n → ℂ, IsAutFormU φ' ∧ ∀ g ∈ finU (E := E) (n := n), φ' g = σ (φ g) := by
  obtain ⟨m, p, e, hpe, hdec⟩ := GlobalTheory.T.autFormDefiniteUnitary_eq_sum_polynomial_mul_autForm E n φ hφ
  choose p' hp' hpp using fun i => GlobalTheory.T.exists_conj_polynomial_definiteUnitary_rational E n σ (p i) (hpe i).1
  obtain ⟨hD, -, -, a, b, -, -, hab, -⟩ := GlobalTheory.T.definiteUnitary_realApprox_and_finite_infinite_split E n
  obtain ⟨φ', hc, hl, hk, hv⟩ := GlobalTheory.T.exists_definiteUnitary_function_polynomial_mul_smooth E n m p' (fun i g => σ (e i g.1)) hp' (fun i => by
    refine ⟨
      { carrier := {k : finU (E := E) (n := n) | RU E n k (e i) = e i}
        one_mem' := by simp
        mul_mem' := fun {x y} hx hy => by
          simp only [Set.mem_setOf_eq] at hx hy ⊢
          rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hy, hx]
        inv_mem' := fun {x} hx => by
          simp only [Set.mem_setOf_eq] at hx ⊢
          conv_lhs => rw [← hx]
          rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, inv_mul_cancel, map_one, Module.End.one_apply] }, ?_, ?_⟩
    · exact (hpe i).2.level
    · intro u hu g
      exact congrArg σ (congrFun (show RU E n u (e i) = e i from hu) g.1))
  have key : ∀ γ ∈ ratU E n, ∀ x : UA E n, cInf x = cInf γ → φ' x = σ (φ x) := by
    intro γ hγ x hx
    have h1 : cInf (b x).1 = cInf γ := by
      rw [← hx]
      conv_rhs => rw [hab x, map_mul, show cInf (a x).1 = 1 from (a x).2, one_mul]
    conv_lhs => rw [hab x, hv]
    set_option synthInstance.maxHeartbeats 100000 in
      conv_rhs => rw [hab x, hdec, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hpp i γ hγ _ h1]
  refine ⟨φ', ⟨hc, fun γ hγ g => ?_, hl, hk⟩, fun g hg => key 1 (one_mem _) g (by rw [map_one]; exact hg)⟩
  have hc2 : Continuous fun x => φ' (γ * x) := hc.comp (continuous_const.mul continuous_id)
  refine congrFun (Continuous.ext_on hD hc2 hc ?_) g
  rintro _ ⟨δ, hδ, u, hu, rfl⟩
  have hu' : cInf u = 1 := hu
  change φ' (γ * (δ * u)) = φ' (δ * u)
  rw [key (γ * δ) (mul_mem hγ hδ) _ (by simp only [map_mul, hu', mul_one]),
    key δ hδ _ (by simp only [map_mul, hu', mul_one]), hφ.left γ hγ]

end GlobalTheory.UnitaryBC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugatesAutomorphicFormSpanFiniteDimensional
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugatesAutomorphicFormSpanFiniteDimensional
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep
open scoped Pointwise

noncomputable section

namespace GlobalTheory.ConjSpan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def gen (t : (E →+* ℂ) × Fin n × Fin n) : infU E n → ℂ := fun x => (cEmb t.1 x.1).val t.2.1 t.2.2

def mono (l : List ((E →+* ℂ) × Fin n × Fin n)) : infU E n → ℂ := (l.map gen).prod


variable (E n) in
def polys (N : ℕ) : Submodule ℂ (infU E n → ℂ) :=
  Submodule.span ℂ (mono '' {l | l.length ≤ N})

theorem polys_fd (N : ℕ) : FiniteDimensional ℂ (polys E n N) :=
  FiniteDimensional.span_of_finite ℂ ((List.finite_length_le _ N).image _)

theorem polys_mono {N N' : ℕ} (h : N ≤ N') : polys E n N ≤ polys E n N' :=
  Submodule.span_mono (Set.image_mono fun _ hl => le_trans hl h)


variable (E n) in
abbrev gens : Set (infU E n → ℂ) := {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}

theorem exists_mono_of_mem_closure {f : infU E n → ℂ} (hf : f ∈ Submonoid.closure (gens E n)) :
    ∃ l, f = mono l := by
  induction hf using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨τ, i, j, rfl⟩ := hf
    exact ⟨[(τ, i, j)], by funext x; simp [mono, gen]⟩
  | one => exact ⟨[], by simp [mono]⟩
  | mul f g _ _ hf hg =>
    obtain ⟨l, rfl⟩ := hf
    obtain ⟨l', rfl⟩ := hg
    exact ⟨l ++ l', by simp [mono]⟩

theorem exists_polys_of_mem_adjoin {p : infU E n → ℂ} (hp : p ∈ Algebra.adjoin ℂ (gens E n)) :
    ∃ N, p ∈ polys E n N := by
  have h : p ∈ Subalgebra.toSubmodule (Algebra.adjoin ℂ (gens E n)) := hp
  rw [Algebra.adjoin_eq_span] at h
  clear hp
  induction h using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨l, rfl⟩ := exists_mono_of_mem_closure hf
    exact ⟨l.length, Submodule.subset_span ⟨l, (le_refl l.length : l.length ≤ l.length), rfl⟩⟩
  | zero => exact ⟨0, zero_mem _⟩
  | add f g _ _ hf hg =>
    obtain ⟨N, hN⟩ := hf
    obtain ⟨N', hN'⟩ := hg
    exact ⟨max N N', add_mem (polys_mono (le_max_left _ _) hN) (polys_mono (le_max_right _ _) hN')⟩
  | smul c f _ hf =>
    obtain ⟨N, hN⟩ := hf
    exact ⟨N, Submodule.smul_mem _ c hN⟩

theorem mono_mem_adjoin (l : List ((E →+* ℂ) × Fin n × Fin n)) : mono l ∈ Algebra.adjoin ℂ (gens E n) := by
  unfold mono
  induction l with
  | nil => simpa using one_mem (Algebra.adjoin ℂ (gens E n))
  | cons t l ih =>
    rw [List.map_cons, List.prod_cons]
    exact mul_mem (Algebra.subset_adjoin ⟨t.1, t.2.1, t.2.2, rfl⟩) ih

theorem polys_le_adjoin (N : ℕ) : polys E n N ≤ Subalgebra.toSubmodule (Algebra.adjoin ℂ (gens E n)) :=
  Submodule.span_le.2 (by rintro _ ⟨l, -, rfl⟩; exact mono_mem_adjoin l)

def conjIdx (σ : ℂ ≃+* ℂ) (t : (E →+* ℂ) × Fin n × Fin n) : (E →+* ℂ) × Fin n × Fin n :=
  (σ.toRingHom.comp t.1, t.2)

theorem mono_conj (σ : ℂ ≃+* ℂ) (l : List ((E →+* ℂ) × Fin n × Fin n)) {γ : UA E n} (hγ : γ ∈ ratU E n)
    (k : infU E n) (hk : cInf k.1 = cInf γ) : mono (l.map (conjIdx σ)) k = σ (mono l k) := by
  induction l with
  | nil => simp [mono]
  | cons t l ih =>
    simp only [mono, List.map_cons, List.prod_cons, Pi.mul_apply] at ih ⊢
    rw [ih, map_mul]
    congr 1
    obtain ⟨x, hx⟩ := exists_cEmb_entry_eq hγ hk t.2.1 t.2.2
    simp only [gen, conjIdx, hx]
    rfl

theorem exists_conj_polys (σ : ℂ ≃+* ℂ) {N : ℕ} {p : infU E n → ℂ} (hp : p ∈ polys E n N) :
    ∃ p' ∈ polys E n N, ∀ γ ∈ ratU E n, ∀ k : infU E n, cInf k.1 = cInf γ → p' k = σ (p k) := by
  induction hp using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨l, hl, rfl⟩ := hf
    exact ⟨mono (l.map (conjIdx σ)), Submodule.subset_span ⟨_, by simpa using hl, rfl⟩,
      fun γ hγ k hk => mono_conj σ l hγ k hk⟩
  | zero => exact ⟨0, zero_mem _, fun _ _ _ _ => by simp⟩
  | add f g _ _ hf hg =>
    obtain ⟨f', hf', hf⟩ := hf
    obtain ⟨g', hg', hg⟩ := hg
    exact ⟨f' + g', add_mem hf' hg', fun γ hγ k hk => by
      rw [Pi.add_apply, Pi.add_apply, map_add (f := _), hf γ hγ k hk, hg γ hγ k hk]⟩
  | smul c f _ hf =>
    obtain ⟨f', hf', hf⟩ := hf
    exact ⟨σ c • f', Submodule.smul_mem _ _ hf', fun γ hγ k hk => by
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, hf γ hγ k hk]⟩

theorem conj_span_finite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (φ : UA E n → ℂ),
    IsAutFormU φ → ∃ M : Submodule ℂ (UA E n → ℂ), FiniteDimensional ℂ M ∧ ∀ (σ : ℂ ≃+* ℂ) (φ' : UA E n → ℂ),
      IsAutFormU φ' → (∀ g ∈ finU (E := E) (n := n), φ' g = σ (φ g)) → φ' ∈ M := by
  intro E _ _ _ n φ hφ
  classical
  obtain ⟨hdense, hdk, -, a, b, -, -, hab, -⟩ := GlobalTheory.UnitarySplit.dense_and_split E n
  obtain ⟨m, p, e, hpe, hdec⟩ := GlobalTheory.UnitaryDecomp.exists_poly_mul_autForm E n φ hφ
  have hcont := (GlobalTheory.PolyRealU.poly_infU E n).1
  choose D hD using fun i => exists_polys_of_mem_adjoin (hpe i).1
  set N := Finset.univ.sup D with hN
  have hpN : ∀ i, p i ∈ polys E n N := fun i => polys_mono (Finset.le_sup (Finset.mem_univ i)) (hD i)
  set K := GlobalTheory.UnitaryDecomp.finStab φ with hK
  obtain ⟨S, hS⟩ := GlobalTheory.DefU.ClassFin.classSet_finite E n K hφ.level
  set S' : Finset (UA E n) := S.image fun s => ((a s : finU (E := E) (n := n)) : UA E n) with hS'
  let M : Submodule ℂ (UA E n → ℂ) :=
    { carrier := {ψ | (∀ γ ∈ ratU E n, ∀ g, ψ (γ * g) = ψ g) ∧ (∀ k ∈ K, ∀ g, ψ (g * (k : UA E n)) = ψ g) ∧
        ∀ s ∈ S', (fun x : infU E n => ψ (s * x)) ∈ polys E n N}
      add_mem' := fun {ψ χ} hψ hχ =>
        ⟨fun γ hγ g => by simp only [Pi.add_apply, hψ.1 γ hγ g, hχ.1 γ hγ g],
          fun k hk g => by simp only [Pi.add_apply, hψ.2.1 k hk g, hχ.2.1 k hk g],
          fun s hs => add_mem (hψ.2.2 s hs) (hχ.2.2 s hs)⟩
      zero_mem' := ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ => zero_mem _⟩
      smul_mem' := fun c ψ hψ =>
        ⟨fun γ hγ g => by simp only [Pi.smul_apply, hψ.1 γ hγ g],
          fun k hk g => by simp only [Pi.smul_apply, hψ.2.1 k hk g],
          fun s hs => Submodule.smul_mem _ c (hψ.2.2 s hs)⟩ }

  have hred : ∀ g : UA E n, ∃ s ∈ S', ∃ y : infU E n, ∀ ψ ∈ M, ψ g = ψ (s * y) := by
    intro g
    obtain ⟨γ, hγ, s, hs, x, hx, k, hk, rfl⟩ := hS g
    refine ⟨((a s : finU (E := E) (n := n)) : UA E n), by rw [hS']; exact Finset.mem_image_of_mem _ hs, ⟨(b s).1 * x, mul_mem (b s).2 hx⟩, fun ψ hψ => ?_⟩
    rw [hψ.2.1 k hk, mul_assoc, hψ.1 γ hγ]
    conv_lhs => rw [hab s]
    simp only [mul_assoc]
  haveI := polys_fd (E := E) (n := n) N
  let f : M →ₗ[ℂ] ((s : S') → polys E n N) :=
    { toFun := fun ψ s => ⟨fun x => ψ.1 (s.1 * x), ψ.2.2.2 s.1 s.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective f := by
    intro ψ χ h
    refine Subtype.ext (funext fun g => ?_)
    obtain ⟨s, hs, y, hy⟩ := hred g
    rw [hy ψ.1 ψ.2, hy χ.1 χ.2]
    exact congrFun (congrArg Subtype.val (congrFun h ⟨s, hs⟩)) y
  refine ⟨M, Module.Finite.of_injective f hinj, fun σ φ' hφ' hagree => ?_⟩

  have hrat : ∀ s ∈ finU (E := E) (n := n), ∀ k : infU E n, ∀ γ ∈ ratU E n, cInf k.1 = cInf γ →
      φ' (s * (k : UA E n)) = σ (φ (s * (k : UA E n))) := by
    intro s hs k γ hγ hk
    have hy : γ⁻¹ * (s * (k : UA E n)) ∈ finU (E := E) (n := n) := by
      have hs1 : cInf s = 1 := hs
      show cInf (γ⁻¹ * (s * (k : UA E n))) = 1
      rw [map_mul, map_mul, map_inv, hs1, hk, one_mul, inv_mul_cancel]
    have e1 : s * (k : UA E n) = γ * (γ⁻¹ * (s * (k : UA E n))) := by group
    rw [e1, hφ'.left γ hγ, hφ.left γ hγ, hagree _ hy]
  refine ⟨hφ'.left, fun k hk => ?_, fun s hs => ?_⟩
  ·
    have hkφ : ∀ x, φ (x * (k : UA E n)) = φ x := fun x => congrFun hk x
    refine congrFun (Continuous.ext_on hdense (hφ'.cont.comp (continuous_mul_const _)) hφ'.cont ?_)
    rintro _ ⟨γ, hγ, x, hx, rfl⟩
    have hxk : x * (k : UA E n) ∈ finU (E := E) (n := n) := mul_mem hx k.2
    simp only [Function.comp_apply]
    rw [mul_assoc, hφ'.left γ hγ, hφ'.left γ hγ, hagree _ hxk, hagree _ hx, hkφ]
  · obtain ⟨s₀, hs₀, rfl⟩ := Finset.mem_image.1 hs
    have hsf : ((a s₀ : finU (E := E) (n := n)) : UA E n) ∈ finU (E := E) (n := n) := (a s₀).2
    choose p' hp'm hp' using fun i => exists_conj_polys σ (hpN i)
    have hq : (∑ i, σ (e i (a s₀)) • p' i) ∈ polys E n N :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hp'm i)
    convert hq using 1
    refine Continuous.ext_on hdk (hφ'.cont.comp (continuous_const.mul continuous_subtype_val))
      (hcont _ (polys_le_adjoin N hq)) ?_
    rintro k ⟨γ, hγ, hk⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hrat _ hsf k γ hγ hk, hdec k, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hp' i γ hγ k hk, mul_comm]

end GlobalTheory.ConjSpan

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugatesAutomorphicFormSpanFiniteDimensionalStatement
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugates_automorphicForm_span_finiteDimensional : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (φ : UA E n → ℂ), IsAutFormU φ → ∃ M : Submodule ℂ (UA E n → ℂ), FiniteDimensional ℂ M ∧ ∀ (σ : ℂ ≃+* ℂ) (φ' : UA E n → ℂ), IsAutFormU φ' → (∀ g ∈ finU (E := E) (n := n), φ' g = σ (φ g)) → φ' ∈ M := by
  first | exact @GlobalTheory.ConjSpan.conj_span_finite | exact GlobalTheory.ConjSpan.conj_span_finite | (intros; apply GlobalTheory.ConjSpan.conj_span_finite; all_goals assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DefiniteUnitaryRationalHeckeCommuteComplexAutomo
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DefiniteUnitaryRationalHeckeCommuteComplexAutomo
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep
open scoped Pointwise

noncomputable section

namespace GlobalTheory.EigenConj

theorem opOf_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (σ : ℂ ≃+* ℂ) (t : UA E n →₀ ℂ), (∀ g ∈ t.support, g ∈ finU (E := E) (n := n) ∧ ∃ q : ℚ, t g = q) → ∀ (φ φ' : UA E n → ℂ) (z : ℂ), IsAutFormU φ → IsAutFormU φ' → (∀ g ∈ finU (E := E) (n := n), φ' g = σ (φ g)) → opOf (RU E n) t φ = z • φ → opOf (RU E n) t φ' = σ z • φ' := by
  intro E _ _ _ n σ t ht φ φ' z hφ hφ' hfin heig
  have key : ∀ (f : UA E n → ℂ) (x : UA E n),
      opOf (RU E n) t f x = ∑ g ∈ t.support, t g * f (x * g) := by
    intro f x
    simp only [opOf, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rfl
  have hc1 : Continuous (opOf (RU E n) t φ') := by
    have e : opOf (RU E n) t φ' = fun x => ∑ g ∈ t.support, t g * φ' (x * g) := funext (key φ')
    rw [e]
    exact continuous_finsetSum _ fun g _ =>
      continuous_const.mul (hφ'.cont.comp (continuous_id.mul continuous_const))
  have hc2 : Continuous (σ z • φ') := hφ'.cont.const_smul _
  have hl1 : ∀ γ ∈ ratU E n, ∀ x, opOf (RU E n) t φ' (γ * x) = opOf (RU E n) t φ' x := by
    intro γ hγ x
    rw [key, key]
    simp_rw [mul_assoc, hφ'.left γ hγ]
  have hl2 : ∀ γ ∈ ratU E n, ∀ x, (σ z • φ') (γ * x) = (σ z • φ') x := by
    intro γ hγ x
    simp only [Pi.smul_apply, hφ'.left γ hγ]
  have hfinEq : ∀ h ∈ finU (E := E) (n := n), opOf (RU E n) t φ' h = (σ z • φ') h := by
    intro h hh
    have e := congrFun heig h
    rw [key, Pi.smul_apply, smul_eq_mul] at e
    rw [key, Pi.smul_apply, smul_eq_mul]
    calc ∑ g ∈ t.support, t g * φ' (h * g) = ∑ g ∈ t.support, σ (t g * φ (h * g)) :=
          Finset.sum_congr rfl fun g hg => by
            obtain ⟨hgU, q, hq⟩ := ht g hg
            rw [map_mul, hfin _ ((finU (E := E) (n := n)).mul_mem hh hgU), hq, map_ratCast]
      _ = σ (∑ g ∈ t.support, t g * φ (h * g)) := (map_sum σ _ _).symm
      _ = σ (z * φ h) := by rw [e]
      _ = σ z * φ' h := by rw [map_mul, hfin h hh]
  have hon : Set.EqOn (opOf (RU E n) t φ') (σ z • φ') ((ratU E n : Set (UA E n)) * (finU (E := E) (n := n) : Set (UA E n))) := by
    rintro _ ⟨γ, hγ, g, hg, rfl⟩
    rw [hl1 γ hγ, hl2 γ hγ]
    exact hfinEq g hg
  exact Continuous.ext_on (GlobalTheory.UnitarySplit.dense_and_split E n).1 hc1 hc2 hon

end GlobalTheory.EigenConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DefiniteUnitaryRationalHeckeCommuteComplexAutomoStatement
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteUnitaryRationalHecke_commute_complexAutomorphism : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (σ : ℂ ≃+* ℂ) (t : UA E n →₀ ℂ), (∀ g ∈ t.support, g ∈ finU (E := E) (n := n) ∧ ∃ q : ℚ, t g = q) → ∀ (φ φ' : UA E n → ℂ) (z : ℂ), IsAutFormU φ → IsAutFormU φ' → (∀ g ∈ finU (E := E) (n := n), φ' g = σ (φ g)) → opOf (RU E n) t φ = z • φ → opOf (RU E n) t φ' = σ z • φ' := by
  first | exact @GlobalTheory.EigenConj.opOf_conj | exact GlobalTheory.EigenConj.opOf_conj | (intros; apply GlobalTheory.EigenConj.opOf_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteAutomorphismOrbitMemFiniteExtensionPadic
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteAutomorphismOrbitMemFiniteExtensionPadic
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.ConjugateSelfDual GlobalTheory.Cong

namespace GlobalTheory

theorem orbit_finite_mem_finite_ext : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (J : Type) (z : J → ℂ),
    (Set.range fun σ : ℂ ≃+* ℂ => fun j => σ (z j)).Finite →
      ∃ L : IntermediateField ℚ_[l] (Qbar l), FiniteDimensional ℚ_[l] L ∧ ∀ j, ι.symm (z j) ∈ L := by
  intro l _ ι J z hfin
  classical
  set O := Set.range fun σ : ℂ ≃+* ℂ => fun j => σ (z j) with hO
  haveI : Finite O := hfin.to_subtype
  set w : J → Qbar l := fun j => ι.symm (z j) with hw
  let K : Finset J → IntermediateField ℚ_[l] (Qbar l) := fun s =>
    IntermediateField.adjoin ℚ_[l] (w '' (s : Set J))
  have hKfin : ∀ s, FiniteDimensional ℚ_[l] (K s) := fun s => by
    haveI : Finite (w '' (s : Set J)) := (s.finite_toSet.image w).to_subtype
    exact IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  have hbound : ∀ s, Module.finrank ℚ_[l] (K s) ≤ Nat.card O := by
    intro s
    haveI := hKfin s
    rw [← AlgHom.card ℚ_[l] (K s) (Qbar l), ← Nat.card_eq_fintype_card]
    let g : (K s →ₐ[ℚ_[l]] Qbar l) → O := fun φ =>
      ⟨fun j => ι (φ.liftNormal (Qbar l) (w j)),
        ι.symm.trans ((AlgEquiv.ofBijective (φ.liftNormal (Qbar l))
          (Algebra.IsAlgebraic.algHom_bijective _)).toRingEquiv.trans ι), rfl⟩
    apply Nat.card_le_card_of_injective g
    intro φ ψ h
    apply IntermediateField.adjoin_algHom_ext
    rintro x ⟨j, hj, rfl⟩
    have h1 := ι.injective (congrFun (congrArg Subtype.val h) j)
    have e1 := AlgHom.liftNormal_commutes φ (Qbar l) ⟨w j, IntermediateField.subset_adjoin _ _ ⟨j, hj, rfl⟩⟩
    have e2 := AlgHom.liftNormal_commutes ψ (Qbar l) ⟨w j, IntermediateField.subset_adjoin _ _ ⟨j, hj, rfl⟩⟩
    simp only [Algebra.algebraMap_self, RingHom.id_apply] at e1 e2
    exact e1.symm.trans (h1.trans e2)
  set R := Set.range fun s : Finset J => Module.finrank ℚ_[l] (K s) with hR
  have hne : R.Nonempty := ⟨_, ∅, rfl⟩
  have hbdd : BddAbove R := ⟨Nat.card O, by rintro _ ⟨s, rfl⟩; exact hbound s⟩
  obtain ⟨s0, hs0⟩ := Nat.sSup_mem hne hbdd
  haveI := hKfin s0
  refine ⟨K s0, inferInstance, fun j => ?_⟩
  have hle : K s0 ≤ K (insert j s0) :=
    IntermediateField.adjoin.mono _ _ _ (Set.image_mono (by simp))
  haveI := hKfin (insert j s0)
  have heq : K s0 = K (insert j s0) := by
    apply IntermediateField.eq_of_le_of_finrank_le hle
    rw [show Module.finrank ℚ_[l] (K s0) = sSup R from hs0]
    exact le_csSup hbdd ⟨insert j s0, rfl⟩
  rw [heq]
  exact IntermediateField.subset_adjoin _ _ ⟨j, by simp, rfl⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteAutomorphismOrbitMemFiniteExtensionPadicStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.ConjugateSelfDual GlobalTheory.Cong
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_automorphism_orbit_mem_finite_extension_padic : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (J : Type) (z : J → ℂ), (Set.range fun σ : ℂ ≃+* ℂ => fun j => σ (z j)).Finite → ∃ L : IntermediateField ℚ_[l] (Qbar l), FiniteDimensional ℚ_[l] L ∧ ∀ j, ι.symm (z j) ∈ L := by
  first | exact @GlobalTheory.orbit_finite_mem_finite_ext | exact GlobalTheory.orbit_finite_mem_finite_ext | (intros; apply GlobalTheory.orbit_finite_mem_finite_ext; all_goals assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LinearIndependentJointEigenvectors
namespace GlobalTheory.JointEigenvectorsIndependentSatakeParameters

theorem linearIndependent_jointEigenvectors {J V : Type} [AddCommGroup V] [Module ℂ V]
    (T : J → V →ₗ[ℂ] V) (S : Set (J → ℂ)) (v : S → V)
    (hv : ∀ χ : S, v χ ≠ 0)
    (hT : ∀ (χ : S) (j : J), T j (v χ) = (χ : J → ℂ) j • v χ) :
    LinearIndependent ℂ v := by
  classical
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro g _ i hi
    simp at hi
  | insert a s ha ih =>
    intro g hg
    rw [Finset.sum_insert ha] at hg
    have e1 : ∑ i ∈ s, g i • v i = -(g a • v a) := eq_neg_of_add_eq_zero_right hg
    have hs : ∀ i ∈ s, g i = 0 := by
      intro i hi
      have hne : (i : J → ℂ) ≠ a := fun h => ha (Subtype.ext h ▸ hi)
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
      have e2 : ∑ i ∈ s, (g i * (i : J → ℂ) j) • v i = -((g a * (a : J → ℂ) j) • v a) := by
        have := congrArg (T j) e1
        set_option synthInstance.maxHeartbeats 100000 in
          simpa [map_sum, map_smul, hT, smul_smul] using this
      have e3 : ∑ i ∈ s, ((a : J → ℂ) j * g i) • v i = -(((a : J → ℂ) j * g a) • v a) := by
        have := congrArg (fun x => (a : J → ℂ) j • x) e1
        simpa [Finset.smul_sum, smul_smul] using this
      have h2 : ∑ i ∈ s, (g i * ((i : J → ℂ) j - (a : J → ℂ) j)) • v i = 0 := by
        calc ∑ i ∈ s, (g i * ((i : J → ℂ) j - (a : J → ℂ) j)) • v i
            = ∑ i ∈ s, (g i * (i : J → ℂ) j) • v i - ∑ i ∈ s, ((a : J → ℂ) j * g i) • v i := by
              rw [← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [← sub_smul]
              congr 1
              ring
          _ = 0 := by rw [e2, e3, mul_comm ((a : J → ℂ) j) (g a)]; exact sub_self _
      have := ih (fun i => g i * ((i : J → ℂ) j - (a : J → ℂ) j)) h2 i hi
      exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hj)
    have hsum : ∑ i ∈ s, g i • v i = 0 := Finset.sum_eq_zero fun i hi => by rw [hs i hi, zero_smul]
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · rw [hsum, add_zero] at hg
      exact (smul_eq_zero.mp hg).resolve_right (hv _)
    · exact hs i hi

end GlobalTheory.JointEigenvectorsIndependentSatakeParameters
end

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong
open scoped Pointwise

noncomputable section

namespace GlobalTheory.Cong

theorem linearIndependent_simulEigen {J V : Type} [AddCommGroup V] [Module ℂ V] (T : J → V →ₗ[ℂ] V)
    (S : Set (J → ℂ)) (v : S → V) (hv : ∀ χ, v χ ≠ 0)
    (hT : ∀ (χ : S) j, T j (v χ) = (χ : J → ℂ) j • v χ) : LinearIndependent ℂ v := by
  first
  | exact @_root_.GlobalTheory.JointEigenvectorsIndependentSatakeParameters.linearIndependent_jointEigenvectors
  | exact _root_.GlobalTheory.JointEigenvectorsIndependentSatakeParameters.linearIndependent_jointEigenvectors
  | (apply _root_.GlobalTheory.JointEigenvectorsIndependentSatakeParameters.linearIndependent_jointEigenvectors <;> assumption)
  | (intros; apply _root_.GlobalTheory.JointEigenvectorsIndependentSatakeParameters.linearIndependent_jointEigenvectors <;> assumption)
  | (intros; apply @_root_.GlobalTheory.JointEigenvectorsIndependentSatakeParameters.linearIndependent_jointEigenvectors <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.JointEigenvectorsIndependentSatakeParameters.linearIndependent_jointEigenvectors ..)

def opLin {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V) (f : Γ →₀ ℂ) :
    V →ₗ[ℂ] V :=
  f.sum fun g c => c • ρ g

theorem opLin_apply {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V) (f : Γ →₀ ℂ)
    (v : V) : opLin ρ f v = opOf ρ f v := by
  simp [opLin, opOf, Finsupp.sum, LinearMap.sum_apply]

theorem eq_zero_of_finU {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {φ : UA E n → ℂ}
    (hφ : IsAutFormU φ) (h0 : ∀ g ∈ finU (E := E) (n := n), φ g = 0) : φ = 0 := by
  refine Continuous.ext_on (GlobalTheory.UnitarySplit.dense_and_split E n).1 hφ.cont continuous_const ?_
  rintro x ⟨γ, hγ, g, hg, rfl⟩
  simp only [Pi.zero_apply]
  rw [hφ.left γ hγ g]
  exact h0 g hg

theorem finU_holds : FinU := by
  intro E _ _ _ l _ ι a _ w₀ K _ lam J t η ht hact U hU
  obtain ⟨φ, hφU, hφ0, hφK⟩ := hU.fix
  have hφ : IsAutFormU φ := hU.aut.aut φ hφU
  have heig : ∀ j, opOf (RU E a) (t j) φ = η U j • φ := fun j => hact U hU.aut φ hφU hφK j
  obtain ⟨g₀, hg₀, hφg₀⟩ : ∃ g ∈ finU (E := E) (n := a), φ g ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφ0 (eq_zero_of_finU hφ h)
  choose φ' hφ' hφ'eq using fun σ : ℂ ≃+* ℂ => exists_conj_isAutFormU E a σ φ hφ
  obtain ⟨M, hMfin, hM⟩ := GlobalTheory.T.conjugates_automorphicForm_span_finiteDimensional E a φ hφ
  have heig' : ∀ σ j, opOf (RU E a) (t j) (φ' σ) = σ (η U j) • φ' σ := fun σ j =>
    GlobalTheory.T.definiteUnitaryRationalHecke_commute_complexAutomorphism E a σ (t j) (ht j) φ (φ' σ) (η U j) hφ (hφ' σ) (hφ'eq σ) (heig j)
  have hne : ∀ σ, φ' σ ≠ 0 := by
    intro σ h
    have e := hφ'eq σ g₀ hg₀
    rw [h, Pi.zero_apply, eq_comm, map_eq_zero_iff σ σ.injective] at e
    exact hφg₀ e
  have hfin : (Set.range fun σ : ℂ ≃+* ℂ => fun j => σ (η U j)).Finite := by
    set S := Set.range fun σ : ℂ ≃+* ℂ => fun j => σ (η U j) with hS
    have hch : ∀ χ : S, ∃ σ : ℂ ≃+* ℂ, (fun j => σ (η U j)) = (χ : J → ℂ) := fun χ => χ.2
    choose sel hsel using hch
    let v : S → (UA E a → ℂ) := fun χ => φ' (sel χ)
    have hli : LinearIndependent ℂ v := by
      refine linearIndependent_simulEigen (fun j => opLin (RU E a) (t j)) S v (fun χ => hne _) ?_
      intro χ j
      rw [opLin_apply, heig', ← hsel χ]
    let v' : S → M := fun χ => ⟨v χ, hM (sel χ) (φ' (sel χ)) (hφ' _) (hφ'eq _)⟩
    have hli' : LinearIndependent ℂ v' := LinearIndependent.of_comp M.subtype hli
    have : Finite S := hli'.finite
    exact Set.toFinite S
  obtain ⟨L, hL, hLmem⟩ := GlobalTheory.T.finite_automorphism_orbit_mem_finite_extension_padic l ι J (η U) hfin
  exact ⟨⟨L, hL⟩, hLmem⟩

end GlobalTheory.Cong
