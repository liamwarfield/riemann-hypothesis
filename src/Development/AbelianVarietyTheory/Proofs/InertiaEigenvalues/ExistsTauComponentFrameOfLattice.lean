module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDecompletionFrameOfLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TmulMemFilV
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NearPiSepComplete

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormCoeAutLeOneIff
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped TensorProduct

namespace GlobalTheory.EigenCoord

theorem exists_basis_mem_iff {O L V : Type} [CommRing O] [IsDomain O] [Field L] [Algebra O L]
    [IsFractionRing O L] [AddCommGroup V] [Module L V] [Module O V] [IsScalarTower O L V]
    (T : Submodule O V) (hfg : T.FG) (hfree : Module.Free O T)
    (hspan : Submodule.span L (T : Set V) = ⊤) :
    ∃ (ρ : ℕ) (t : Module.Basis (Fin ρ) L V),
      ∀ v, v ∈ T ↔ ∀ i, ∃ o : O, algebraMap O L o = t.repr v i := by
  haveI : Module.Finite O T := Module.Finite.iff_fg.mpr hfg
  let c := Module.finBasis O T
  have hli : LinearIndependent O (fun i => (c i : V)) :=
    c.linearIndependent.map' T.subtype (Submodule.ker_subtype T)
  have hli' : LinearIndependent L (fun i => (c i : V)) :=
    (LinearIndependent.iff_fractionRing O L).mp hli
  have hsum : ∀ x : T, (x : V) = ∑ i, algebraMap O L (c.repr x i) • (c i : V) := by
    intro x
    have h := congrArg T.subtype (c.sum_repr x)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h
    simp only [map_smul, Submodule.subtype_apply] at h
    simp only [algebraMap_smul]
    exact h.symm
  have hsp : ⊤ ≤ Submodule.span L (Set.range fun i => (c i : V)) := by
    rw [← hspan, Submodule.span_le]
    intro x hx
    rw [SetLike.mem_coe, show x = ((⟨x, hx⟩ : T) : V) from rfl, hsum]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let t := Module.Basis.mk hli' hsp
  have ht : ∀ i, t i = (c i : V) := fun i => Module.Basis.mk_apply hli' hsp i
  refine ⟨_, t, fun v => ⟨fun hv i => ⟨c.repr ⟨v, hv⟩ i, ?_⟩, fun h => ?_⟩⟩
  · have h1 : v = ∑ j, algebraMap O L (c.repr ⟨v, hv⟩ j) • t j := by
      simp only [ht]
      exact hsum ⟨v, hv⟩
    have h2 := congrFun (t.repr_sum_self (fun j => algebraMap O L (c.repr ⟨v, hv⟩ j))) i
    rw [← h1] at h2
    exact h2.symm
  · choose o ho using h
    rw [← t.sum_repr v]
    refine T.sum_mem fun i _ => ?_
    rw [← ho, algebraMap_smul, ht]
    exact T.smul_mem _ (c i).2

theorem norm_coe_aut_le_one_iff {l : ℕ} [Fact l.Prime] (ι : GQ l) (x : Om l) :
    ‖((ι x : Om l) : PadicComplex l)‖ ≤ 1 ↔ ‖x‖ ≤ 1 := by
  rw [PadicComplex.norm_extends, ← isIntegral_padicInt_iff_norm_le_one,
    ← isIntegral_padicInt_iff_norm_le_one]
  exact isIntegral_algHom_iff (ι.toAlgHom.restrictScalars ℤ_[l]) ι.injective

theorem exists_matrix_of_basis {F L C V : Type} [NormedField F] [Field L] [NormedField C]
    [Algebra F L] [Algebra F C] [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]
    (S : Set V) {d ρ : ℕ} (b : Module.Basis (Fin d) F V) (t : Module.Basis (Fin ρ) L V)
    (φ : L →ₐ[F] C) (hb : ∀ v, v ∈ S ↔ ∀ i, ‖b.repr v i‖ ≤ 1)
    (hmem : ∀ v, v ∈ S ↔ ∀ i, ‖φ (t.repr v i)‖ ≤ 1) :
    ∃ Pr : Matrix (Fin ρ) (Fin d) C, (∀ i j, ‖Pr i j‖ ≤ 1) ∧
      (∀ a : L, Pr * Matrix.of (fun i k : Fin d => algebraMap F C (b.repr (a • b k) i)) =
        φ a • Pr) ∧
      ∀ y : Fin d → F, (∀ i, ‖Pr.mulVec (fun a => algebraMap F C (y a)) i‖ ≤ 1) →
        ∀ a, ‖y a‖ ≤ 1 := by
  have key : ∀ (y : Fin d → F) (i : Fin ρ),
      ∑ j, φ (t.repr (b j) i) * algebraMap F C (y j) = φ (t.repr (∑ j, y j • b j) i) := by
    intro y i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finsupp.finsetSum_apply, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← algebraMap_smul L (y j), map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul,
      AlgHom.commutes, mul_comm]
  refine ⟨Matrix.of fun i j => φ (t.repr (b j) i), fun i j => ?_, fun a => ?_, fun y hy a => ?_⟩
  · refine (hmem _).mp ((hb _).mpr fun k => ?_) i
    rw [b.repr_self, Finsupp.single_apply]
    split_ifs <;> simp
  · ext i k
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply, Matrix.smul_apply]
    rw [key, b.sum_repr, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, smul_eq_mul]
  · have hv : (∑ j, y j • b j) ∈ S := by
      refine (hmem _).mpr fun i => ?_
      rw [← key]
      exact hy i
    have := (hb _).mp hv a
    rwa [congrFun (b.repr_sum_self y) a] at this

theorem exists_matrix : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (d : ℕ) (b : Module.Basis (Fin d) ℚ_[l] T.V), (∀ v : T.V, v ∈ T.L.T ↔ ∀ i, ‖b.repr v i‖ ≤ 1) → ∀ ι : GQ l, ∃ (ρ : ℕ) (Pr : Matrix (Fin ρ) (Fin d) (PadicComplex l)), (∀ i j, ‖Pr i j‖ ≤ 1) ∧ (∀ a : ↥LL.1, Pr * Matrix.of (fun i k : Fin d => algebraMap ℚ_[l] (PadicComplex l) (b.repr (a • b k) i)) = ((ι (a : Om l) : Om l) : PadicComplex l) • Pr) ∧ ∀ y : Fin d → ℚ_[l], (∀ i, ‖Pr.mulVec (fun a => algebraMap ℚ_[l] (PadicComplex l) (y a)) i‖ ≤ 1) → ∀ a, ‖y a‖ ≤ 1 := by
  intro l _ K LL T d b hb ι
  haveI := LL.2
  haveI : IsFractionRing (OL LL) LL.1 := isFractionRing_integralClosure_padicInt l LL.1
  obtain ⟨ρ, t, ht⟩ := exists_basis_mem_iff (L := LL.1) T.L.T T.L.fg T.L.free T.L.span
  let φ : LL.1 →ₐ[ℚ_[l]] PadicComplex l :=
    (IsScalarTower.toAlgHom ℚ_[l] (Om l) (PadicComplex l)).comp (ι.toAlgHom.comp LL.1.val)
  have hφ : ∀ x : LL.1, φ x = ((ι (x : Om l) : Om l) : PadicComplex l) := fun _ => rfl
  have hmem : ∀ v, v ∈ T.L.T ↔ ∀ i, ‖φ (t.repr v i)‖ ≤ 1 := by
    intro v
    rw [ht]
    refine forall_congr' fun i => ?_
    rw [hφ, norm_coe_aut_le_one_iff, ← mem_integralClosure_padicInt_iff]
    exact ⟨fun ⟨o, ho⟩ => ho ▸ o.2, fun h => ⟨⟨_, h⟩, rfl⟩⟩
  exact ⟨ρ, exists_matrix_of_basis (T.L.T : Set T.V) b t φ hb hmem⟩

end GlobalTheory.EigenCoord
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSubBasis
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open Matrix

noncomputable section

namespace GlobalTheory.TauFrame

theorem exists_sub_basis {C : Type} [Field C] {d r : ℕ} (f : Fin d → Fin r → C)
    (hf : Submodule.span C (Set.range f) = ⊤) :
    ∃ κ : Fin r → Fin d, LinearIndependent C (fun k => f (κ k)) := by
  obtain ⟨ι, a, ha, hsp, hli⟩ := exists_linearIndependent' C f
  haveI : Finite ι := Finite.of_injective a ha
  haveI := Fintype.ofFinite ι
  have hb := Module.finrank_eq_card_basis (Module.Basis.mk hli (by rw [hsp, hf]))
  rw [Module.finrank_fin_fun] at hb
  let e : Fin r ≃ ι := (Fintype.equivFinOfCardEq hb.symm).symm
  exact ⟨a ∘ e, hli.comp e e.injective⟩

section Norm

variable {C : Type} [NormedField C] [IsUltrametricDist C]

theorem norm_sum_le {n : ℕ} (f : Fin n → C) {c : ℝ} (hc : 0 ≤ c) (h : ∀ i, ‖f i‖ ≤ c) :
    ‖∑ i, f i‖ ≤ c :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hc (fun i _ => h i)

theorem norm_mul_le {a b c : ℕ} (A : Matrix (Fin a) (Fin b) C) (B : Matrix (Fin b) (Fin c) C)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hA : ∀ i j, ‖A i j‖ ≤ x) (hB : ∀ i j, ‖B i j‖ ≤ y) (i j) :
    ‖(A * B) i j‖ ≤ x * y := by
  rw [Matrix.mul_apply]
  refine norm_sum_le _ (mul_nonneg hx hy) fun k => ?_
  rw [norm_mul]
  exact mul_le_mul (hA _ _) (hB _ _) (norm_nonneg _) hx

theorem norm_mulVec_le {a b : ℕ} (A : Matrix (Fin a) (Fin b) C) (v : Fin b → C)
    (hA : ∀ i j, ‖A i j‖ ≤ 1) (hv : ∀ i, ‖v i‖ ≤ 1) (i) : ‖A.mulVec v i‖ ≤ 1 := by
  simp only [Matrix.mulVec, dotProduct]
  refine norm_sum_le _ zero_le_one fun k => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hA _ _) (norm_nonneg _) (hv _)

theorem exists_bound_lt {a : ℕ} (A : Matrix (Fin a) (Fin a) C) {ρ : ℝ} (hρ : 0 < ρ)
    (h : ∀ i j, ‖A i j‖ < ρ) : ∃ x, 0 ≤ x ∧ x < ρ ∧ ∀ i j, ‖A i j‖ ≤ x := by
  refine ⟨‖fun p : Fin a × Fin a => A p.1 p.2‖, norm_nonneg _, ?_, fun i j => ?_⟩
  · exact (pi_norm_lt_iff hρ).2 fun p => h _ _
  · exact norm_le_pi_norm (fun p : Fin a × Fin a => A p.1 p.2) (i, j)

end Norm

theorem mem_mul {C : Type} [Field C] (F : Subfield C) {a b c : ℕ} (A : Matrix (Fin a) (Fin b) C)
    (B : Matrix (Fin b) (Fin c) C) (hA : ∀ i j, A i j ∈ F) (hB : ∀ i j, B i j ∈ F) (i j) :
    (A * B) i j ∈ F := by
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => mul_mem (hA _ _) (hB _ _)

variable {l : ℕ} [Fact l.Prime]

def subC (F : IntermediateField ℚ_[l] (Om l)) : Subfield (PadicComplex l) :=
  F.toSubfield.map (algebraMap (Om l) (PadicComplex l))

theorem mem_subC {F : IntermediateField ℚ_[l] (Om l)} {y : PadicComplex l} :
    y ∈ subC F ↔ y ∈ inC F := Iff.rfl

theorem act_fix {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (ha : IsActC act)
    {F : IntermediateField ℚ_[l] (Om l)} {σ : GQ l} (hσ : σ ∈ F.fixingSubgroup)
    {y : PadicComplex l} (hy : y ∈ subC F) : act σ y = y := by
  obtain ⟨x, hx, rfl⟩ := hy
  have h1 := ha.1 σ x
  have h2 : σ x = x := hσ ⟨x, hx⟩
  rw [h2] at h1
  exact h1

theorem map_mul' {a b c : ℕ} (f : PadicComplex l ≃+* PadicComplex l)
    (A : Matrix (Fin a) (Fin b) (PadicComplex l)) (B : Matrix (Fin b) (Fin c) (PadicComplex l)) :
    (A * B).map f = A.map f * B.map f := by
  ext i j
  simp [Matrix.mul_apply]

theorem frame_of_idem (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ)
    (ha : IsActC act) (K : FinExt l) (m d r : ℕ)
    (M U : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l))
    (Dm E : Matrix (Fin d) (Fin d) (PadicComplex l)) (g : GQ l) (hD : IsDec act χ K m M Dm U g)
    (hEM : ∀ σ ∈ Gj K m, E * M σ = M σ * E) (hEσ : ∀ σ ∈ Gj K m, E.map (act σ) = E)
    (hEF : ∀ i j, (Dm⁻¹ * E * Dm) i j ∈ subC (Ks K m))
    (R : Matrix (Fin r) (Fin d) (PadicComplex l)) (S : Matrix (Fin d) (Fin r) (PadicComplex l))
    (hR : ∀ i j, R i j ∈ subC (Ks K m) ∧ ‖R i j‖ ≤ 1)
    (hS : ∀ i j, S i j ∈ subC (Ks K m) ∧ ‖S i j‖ ≤ 1)
    (hRS : R * S = 1) (hRe : R * (Dm⁻¹ * E * Dm) = R) (heSR : (Dm⁻¹ * E * Dm) * S * R = Dm⁻¹ * E * Dm)
    (e : Fin d → Fin d → PadicComplex l) (u : Fin d → ℤ) (hli : LinearIndependent (PadicComplex l) e)
    (hfix : ∀ σ ∈ Gj K m, ∀ k, twAct act χ (u k) M σ (e k) = e k) (J : Set ℤ)
    (hJ : ∀ k, E.mulVec (e k) ≠ 0 → u k ∈ J) :
    Frame χ K m (fun σ => R * U σ * S) g ∧ HTBasis act χ (Gj K m) (fun σ => R * U σ * S) J ∧
    (∀ σ ∈ Gj K m, (R * Dm⁻¹) * M σ = (R * U σ * S) * (R * Dm⁻¹).map (act σ)) ∧
    ball l r ⊆ (R * Dm⁻¹).mulVec '' ball l d ∧
    (∀ x ∈ ball l d, (l : PadicComplex l) • (R * Dm⁻¹).mulVec x ∈ ball l r) ∧
    ∃ Q : Matrix (Fin d) (Fin r) (PadicComplex l), Q * (R * Dm⁻¹) = E := by
  obtain ⟨hdet, hDi, hDl, ⟨hgen, hcont, hint, hmul, hH, hg⟩, hrel⟩ := hD
  set e' := Dm⁻¹ * E * Dm with he'
  have h1 : Dm * Dm⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have h2 : Dm⁻¹ * Dm = 1 := Matrix.nonsing_inv_mul _ hdet
  have hDe : Dm * e' = E * Dm := by
    rw [he', ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hfixm : ∀ σ ∈ Gj K m, ∀ {a b : ℕ} (X : Matrix (Fin a) (Fin b) (PadicComplex l)),
      (∀ i j, X i j ∈ subC (Ks K m)) → X.map (act σ) = X := by
    intro σ hσ a b X hX
    ext i j
    exact act_fix ha hσ (hX i j)
  have hcomm : ∀ σ ∈ Gj K m, e' * U σ = U σ * e' := by
    intro σ hσ
    have : Dm * (e' * U σ) = Dm * (U σ * e') := by
      rw [← Matrix.mul_assoc, hDe, Matrix.mul_assoc, hrel σ hσ, ← Matrix.mul_assoc, hEM σ hσ,
        Matrix.mul_assoc, ← Matrix.mul_assoc Dm, hrel σ hσ, Matrix.mul_assoc]
      congr 1
      conv_lhs => rw [← hEσ σ hσ]
      conv_rhs => rw [← hfixm σ hσ e' hEF]
      rw [← map_mul', ← map_mul', hDe]
    have h3 := congrArg (fun X => Dm⁻¹ * X) this
    simpa only [← Matrix.mul_assoc, h2, Matrix.one_mul] using h3
  have hkey : ∀ σ ∈ Gj K m, R * U σ * S * R = R * U σ := by
    intro σ hσ
    have h3 : R * U σ = R * U σ * e' := by
      rw [Matrix.mul_assoc, ← hcomm σ hσ, ← Matrix.mul_assoc, hRe]
    calc R * U σ * S * R = R * U σ * (e' * S * R) := by
          conv_lhs => rw [h3]
          simp only [Matrix.mul_assoc]
      _ = R * U σ := by rw [heSR, ← h3]
  have heq : ∀ σ ∈ Gj K m, (R * Dm⁻¹) * M σ = (R * U σ * S) * (R * Dm⁻¹).map (act σ) := by
    intro σ hσ
    have h3 : Dm.map (act σ) * Dm⁻¹.map (act σ) = 1 := by
      rw [← map_mul', h1]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    have h4 : Dm⁻¹ * M σ = U σ * Dm⁻¹.map (act σ) := by
      calc Dm⁻¹ * M σ = Dm⁻¹ * (M σ * Dm.map (act σ)) * Dm⁻¹.map (act σ) := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, h3, Matrix.mul_one]
        _ = _ := by rw [← hrel σ hσ, ← Matrix.mul_assoc, h2, Matrix.one_mul]
    rw [map_mul', hfixm σ hσ R (fun i j => (hR i j).1), ← Matrix.mul_assoc, hkey σ hσ,
      Matrix.mul_assoc, h4, Matrix.mul_assoc]
  have hsec : R * Dm⁻¹ * (Dm * S) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Dm⁻¹, h2, Matrix.one_mul, hRS]
  refine ⟨⟨hgen, ?_, ?_, ?_, ?_, ?_⟩, ?_, heq, ?_, ?_, ?_⟩
  · intro a b
    simp only [Matrix.mul_apply]
    refine continuousOn_finsetSum _ fun k _ => ContinuousOn.mul ?_ continuousOn_const
    exact continuousOn_finsetSum _ fun j _ => ContinuousOn.mul continuousOn_const (hcont _ _)
  · intro σ hσ a b
    refine ⟨mem_subC.1 (mem_mul _ _ _ (mem_mul _ _ _ (fun i j => (hR i j).1)
      (fun i j => mem_subC.2 (hint σ hσ i j).1)) (fun i j => (hS i j).1) a b), ?_⟩
    have := norm_mul_le (R * U σ) S (mul_nonneg zero_le_one zero_le_one) zero_le_one
      (norm_mul_le R (U σ) zero_le_one zero_le_one (fun i j => (hR i j).2)
        (fun i j => (hint σ hσ i j).2)) (fun i j => (hS i j).2) a b
    simpa using this
  · intro σ hσ τ hτ
    simp only
    rw [hmul σ hσ τ hτ, ← Matrix.mul_assoc (R * U σ * S), ← Matrix.mul_assoc (R * U σ * S),
      hkey σ hσ]
    simp only [Matrix.mul_assoc]
  · intro σ hσ
    simp only
    rw [hH σ hσ, Matrix.mul_one, hRS]
  · intro a b
    have hrho : 0 < rho1 l :=
      Real.rpow_pos_of_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _
    obtain ⟨x, hx0, hx, hxb⟩ := exists_bound_lt (U g - 1) hrho hg
    have h3 : R * U g * S - 1 = R * (U g - 1) * S := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hRS]
    simp only
    rw [h3]
    have := norm_mul_le (R * (U g - 1)) S (mul_nonneg zero_le_one hx0) zero_le_one
      (norm_mul_le R (U g - 1) zero_le_one hx0 (fun i j => (hR i j).2) hxb)
      (fun i j => (hS i j).2) a b
    exact lt_of_le_of_lt (by simpa using this) hx
  · set Pm := R * Dm⁻¹ with hPm
    have hsp : Submodule.span (PadicComplex l) (Set.range fun k => Pm.mulVec (e k)) = ⊤ := by
      have h3 : Submodule.span (PadicComplex l) (Set.range e) = ⊤ :=
        hli.span_eq_top_of_card_eq_finrank' (by simp)
      have h4 : (Set.range fun k => Pm.mulVec (e k)) = Pm.mulVecLin '' Set.range e := by
        rw [← Set.range_comp]; rfl
      rw [h4, ← Submodule.map_span, h3, Submodule.map_top, LinearMap.range_eq_top]
      intro y
      refine ⟨(Dm * S).mulVec y, ?_⟩
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hsec, Matrix.one_mulVec]
    obtain ⟨κ, hκ⟩ := exists_sub_basis _ hsp
    refine ⟨fun k => Pm.mulVec (e (κ k)), fun k => u (κ k), hκ, fun k => hJ _ fun h0 => ?_, ?_⟩
    · apply hκ.ne_zero k
      have h3 : Pm * E = Pm := by
        calc Pm * E = R * e' * Dm⁻¹ := by
              rw [hPm, he']; simp only [Matrix.mul_assoc, h1, Matrix.mul_one]
          _ = Pm := by rw [hRe]
      show Pm.mulVec (e (κ k)) = 0
      rw [← h3, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
    · intro σ hσ k
      have h3 := hfix σ hσ (κ k)
      unfold twAct at h3 ⊢
      have hmap : (fun a => act σ (Pm.mulVec (e (κ k)) a)) =
          (Pm.map (act σ)).mulVec (fun a => act σ (e (κ k) a)) := by
        funext a
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
      simp only
      rw [hmap, Matrix.mulVec_mulVec, ← heq σ hσ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul, h3]
  · intro y hy
    refine ⟨Dm.mulVec (S.mulVec y), norm_mulVec_le _ _ hDi
      (norm_mulVec_le _ _ (fun i j => (hS i j).2) hy), ?_⟩
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, hsec, Matrix.one_mulVec]
  · intro x hx
    have h3 : (l : PadicComplex l) • (R * Dm⁻¹).mulVec x =
        R.mulVec (((l : PadicComplex l) • Dm⁻¹).mulVec x) := by
      rw [Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
    rw [h3]
    exact norm_mulVec_le _ _ (fun i j => (hR i j).2) (norm_mulVec_le _ _ (fun i j => hDl i j) hx)
  · refine ⟨Dm * e' * S, ?_⟩
    calc Dm * e' * S * (R * Dm⁻¹) = Dm * (e' * S * R) * Dm⁻¹ := by simp only [Matrix.mul_assoc]
      _ = E := by rw [heSR, hDe, Matrix.mul_assoc, h1, Matrix.mul_one]

end GlobalTheory.TauFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralFactorOfIdempotentSubfield
namespace GlobalTheory

private theorem cur_decomposition_of_maximal_minor {K : Type} [Field K] {d r : ℕ} (e : Matrix (Fin d) (Fin d) K)
    (τ σ : Fin r → Fin d) (hA : (e.submatrix τ σ).det ≠ 0)
    (hmax : ∀ τ' σ' : Fin (r + 1) → Fin d, (e.submatrix τ' σ').det = 0) :
    e.submatrix id σ * (e.submatrix τ σ)⁻¹ * e.submatrix τ id = e := by
  ext i j
  set A := e.submatrix τ σ with hAdef
  let B : Matrix (Fin r) (Fin 1) K := Matrix.of fun k _ => e (τ k) j
  let C : Matrix (Fin 1) (Fin r) K := Matrix.of fun _ l => e i (σ l)
  let D : Matrix (Fin 1) (Fin 1) K := Matrix.of fun _ _ => e i j
  have hM : Matrix.fromBlocks A B C D =
      e.submatrix (Sum.elim τ fun _ => i) (Sum.elim σ fun _ => j) := by
    ext (a | a) (b | b) <;> rfl
  have h0 : (Matrix.fromBlocks A B C D).det = 0 := by
    rw [hM, ← Matrix.det_reindex_self finSumFinEquiv, Matrix.reindex_apply,
      Matrix.submatrix_submatrix]
    exact hmax _ _
  have : Invertible A := A.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr hA)
  rw [Matrix.det_fromBlocks₁₁, Matrix.det_fin_one, Matrix.invOf_eq_nonsing_inv] at h0
  have h1 := (mul_eq_zero.mp h0).resolve_left hA
  rw [Matrix.sub_apply, sub_eq_zero] at h1
  have h2 : (C * A⁻¹ * B) 0 0 = (e.submatrix id σ * A⁻¹ * e.submatrix τ id) i j := rfl
  rw [← h2, ← h1]
  rfl

private theorem inv_mul_submatrix_apply_eq_det_ratio {K : Type} [Field K] {d r : ℕ}
    (e : Matrix (Fin d) (Fin d) K) (τ σ : Fin r → Fin d) (k : Fin r) (j : Fin d) :
    ((e.submatrix τ σ)⁻¹ * e.submatrix τ id) k j =
      (e.submatrix τ σ).det⁻¹ * (e.submatrix τ (Function.update σ k j)).det := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  congr 1
  change (Matrix.mulVec (e.submatrix τ σ).adjugate fun l => e (τ l) j) k = _
  rw [← Matrix.cramer_eq_adjugate_mulVec, Matrix.cramer_apply]
  congr 1
  ext a c
  by_cases h : c = k
  · subst h; simp
  · simp [h]

theorem exists_integral_factor_of_idempotent {K : Type} [Field K] (O : ValuationSubring K) (d : ℕ)
    (e : Matrix (Fin d) (Fin d) K) (he : e * e = e) :
    ∃ (r : ℕ) (R : Matrix (Fin r) (Fin d) K) (S : Matrix (Fin d) (Fin r) K),
      (∀ i j, R i j ∈ O) ∧ (∀ i j, S i j ∈ O) ∧ R * S = 1 ∧ R * e = R ∧ e * S * R = e := by
  classical
  let P : ℕ → Prop := fun k => ∃ τ σ : Fin k → Fin d, (e.submatrix τ σ).det ≠ 0
  set r := Nat.findGreatest P d with hr
  have hPr : P r := Nat.findGreatest_spec (m := 0) (Nat.zero_le _) ⟨Fin.elim0, Fin.elim0, by simp⟩
  have hnot : ∀ τ σ : Fin (r + 1) → Fin d, (e.submatrix τ σ).det = 0 := by
    intro τ σ
    by_contra hne
    by_cases hle : r + 1 ≤ d
    · exact Nat.findGreatest_is_greatest (Nat.lt_succ_self r) hle ⟨τ, σ, hne⟩
    · obtain ⟨a, b, hab, hτ⟩ := Fintype.exists_ne_map_eq_of_card_lt τ (by simp; omega)
      exact hne (Matrix.det_zero_of_row_eq hab (by funext c; simp [hτ]))
  let v := O.valuation
  obtain ⟨τ0, σ0, h0⟩ := hPr
  obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ
    (fun p : (Fin r → Fin d) × (Fin r → Fin d) => v (e.submatrix p.1 p.2).det)
    ⟨(τ0, σ0), Finset.mem_univ _⟩
  obtain ⟨τ, σ⟩ := p
  have hA : (e.submatrix τ σ).det ≠ 0 := by
    intro hz
    have hle := hp (τ0, σ0) (Finset.mem_univ _)
    simp only [hz, map_zero] at hle
    exact h0 ((Valuation.zero_iff _).mp (le_antisymm hle zero_le))
  have hv : v (e.submatrix τ σ).det ≠ 0 := (Valuation.ne_zero_iff _).mpr hA
  let S : Matrix (Fin d) (Fin r) K := Matrix.of fun i k => if i = σ k then 1 else 0
  have hS : ∀ {m : Type} [Fintype m] (M : Matrix m (Fin d) K), M * S = M.submatrix id σ := by
    intro m _ M
    ext a k
    simp [S, Matrix.mul_apply]
  refine ⟨r, (e.submatrix τ σ)⁻¹ * e.submatrix τ id, S, ?_, ?_, ?_, ?_, ?_⟩
  · intro k j
    rw [inv_mul_submatrix_apply_eq_det_ratio, ← O.valuation_le_one_iff, map_mul, map_inv₀]
    have hle := hp (τ, Function.update σ k j) (Finset.mem_univ _)
    calc (v (e.submatrix τ σ).det)⁻¹ * v (e.submatrix τ (Function.update σ k j)).det
        ≤ (v (e.submatrix τ σ).det)⁻¹ * v (e.submatrix τ σ).det := mul_le_mul_right hle _
      _ = 1 := inv_mul_cancel₀ hv
  · intro i k
    simp only [S, Matrix.of_apply]
    split_ifs
    · exact O.one_mem
    · exact O.zero_mem
  · rw [Matrix.mul_assoc, hS]
    exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA)
  · rw [Matrix.mul_assoc]
    congr 1
    ext a c
    change (e * e) (τ a) c = e (τ a) c
    rw [he]
  · rw [hS, ← Matrix.mul_assoc]
    exact cur_decomposition_of_maximal_minor e τ σ hA hnot

theorem exists_integral_factor_of_idempotent_subfield (C : Type) [NormedField C]
    [IsUltrametricDist C] (F : Subfield C) (d : ℕ) (e : Matrix (Fin d) (Fin d) C)
    (hF : ∀ i j, e i j ∈ F) (he : e * e = e) :
    ∃ (r : ℕ) (R : Matrix (Fin r) (Fin d) C) (S : Matrix (Fin d) (Fin r) C),
      (∀ i j, R i j ∈ F ∧ ‖R i j‖ ≤ 1) ∧ (∀ i j, S i j ∈ F ∧ ‖S i j‖ ≤ 1) ∧
        R * S = 1 ∧ R * e = R ∧ e * S * R = e := by
  obtain ⟨e', rfl⟩ : ∃ e' : Matrix (Fin d) (Fin d) F, e'.map F.subtype = e :=
    ⟨Matrix.of fun i j => ⟨e i j, hF i j⟩, by ext; rfl⟩
  let O : ValuationSubring F :=
    { carrier := {x | ‖(x : C)‖ ≤ 1}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, Subfield.coe_mul, norm_mul] at *
        calc ‖(a : C)‖ * ‖(b : C)‖ ≤ 1 * 1 := mul_le_mul ha hb (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      one_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, Subfield.coe_add] at *
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by simpa using ha
      mem_or_inv_mem' := fun x => by
        rcases le_or_gt ‖(x : C)‖ 1 with h | h
        · exact Or.inl h
        · right
          change ‖((x⁻¹ : F) : C)‖ ≤ 1
          rw [Subfield.coe_inv, norm_inv]
          exact inv_le_one_of_one_le₀ h.le }
  have hinj : Function.Injective (F.subtype : F → C) := Subtype.val_injective
  have he' : e' * e' = e' := Matrix.map_injective hinj (by
    change (e' * e').map F.subtype = e'.map F.subtype
    rw [Matrix.map_mul, he])
  obtain ⟨r, R, S, hR, hS, hRS, hRe, heSR⟩ := exists_integral_factor_of_idempotent O d e' he'
  refine ⟨r, R.map F.subtype, S.map F.subtype, fun i j => ⟨(R i j).2, hR i j⟩,
    fun i j => ⟨(S i j).2, hS i j⟩, ?_, ?_, ?_⟩
  · rw [← Matrix.map_mul, hRS, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [← Matrix.map_mul, hRe]
  · rw [← Matrix.map_mul, ← Matrix.map_mul, heSR]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTauComponentFrameOfLattice
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TauFrame

theorem exists_sep_elem (F K : Type) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [Algebra.IsSeparable F K] :
    ∃ (n : ℕ) (α β : Fin n → K),
      (∀ κ : K, ∑ j, (κ * α j) ⊗ₜ[F] β j = ∑ j, α j ⊗ₜ[F] (κ * β j)) ∧ ∑ j, α j * β j = 1 := by
  haveI := Algebra.FormallyUnramified.of_isSeparable F K
  obtain ⟨n, α, β, h⟩ := TensorProduct.exists_sum_tmul_eq (Algebra.FormallyUnramified.elem F K)
  refine ⟨n, α, β, fun κ => ?_, ?_⟩
  · have := Algebra.FormallyUnramified.one_tmul_mul_elem (R := F) (S := K) κ
    rw [h] at this
    simp only [Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul, one_mul] at this
    exact this.symm
  · have := Algebra.FormallyUnramified.lmul_elem (R := F) (S := K)
    rw [h] at this
    simpa using this

theorem sep_idem {F K C R : Type} [Field F] [Field K] [Algebra F K] [CommRing C] [Ring R]
    [Algebra F C] [Algebra C R] [Algebra F R] [IsScalarTower F C R] (B : K →ₐ[F] R) (j : K →ₐ[F] C)
    {n : ℕ} (α β : Fin n → K)
    (h1 : ∀ κ : K, ∑ i, (κ * α i) ⊗ₜ[F] β i = ∑ i, α i ⊗ₜ[F] (κ * β i)) (h2 : ∑ i, α i * β i = 1) :
    (∑ i, j (β i) • B (α i)) * (∑ i, j (β i) • B (α i)) = ∑ i, j (β i) • B (α i) := by
  set E := ∑ i, j (β i) • B (α i) with hE
  let φ : K ⊗[F] K →ₗ[F] R := TensorProduct.lift (LinearMap.mk₂ F (fun a c => j c • B a)
    (fun a a' c => by simp [smul_add]) (fun r a c => by rw [map_smul, smul_comm])
    (fun a c c' => by simp [add_smul]) (fun r a c => by rw [map_smul, smul_assoc]))
  have hφ : ∀ a c, φ (a ⊗ₜ c) = j c • B a := fun a c => rfl
  have key : ∀ κ, B κ * E = j κ • E := by
    intro κ
    have := congrArg φ (h1 κ)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, hφ, map_mul] at this
    rw [hE, Finset.mul_sum, Finset.smul_sum]
    simp only [mul_smul_comm, smul_smul]
    exact this
  calc E * E = ∑ i, j (β i) • (B (α i) * E) := by
        conv_lhs => rw [hE, Finset.sum_mul]
        simp only [smul_mul_assoc, hE]
    _ = j (∑ i, α i * β i) • E := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [key, smul_smul, map_sum, map_mul, Finset.sum_smul, mul_comm]
    _ = E := by rw [h2, map_one, one_smul]

def mulMat {F LL V : Type} (C : Type) [Field F] [Field LL] [Algebra F LL] [AddCommGroup V]
    [Module LL V] [Module F V] [IsScalarTower F LL V] [CommRing C] [Algebra F C] {d : ℕ}
    (b : Module.Basis (Fin d) F V) : LL →ₐ[F] Matrix (Fin d) (Fin d) C :=
  ((Algebra.ofId F C).mapMatrix.comp (LinearMap.toMatrixAlgEquiv b).toAlgHom).comp
    (Algebra.lsmul F F V)

theorem mulMat_eq {F LL V : Type} (C : Type) [Field F] [Field LL] [Algebra F LL] [AddCommGroup V]
    [Module LL V] [Module F V] [IsScalarTower F LL V] [CommRing C] [Algebra F C] {d : ℕ}
    (b : Module.Basis (Fin d) F V) (a : LL) :
    mulMat C b a = Matrix.of fun i k => algebraMap F C (b.repr (a • b k) i) := by
  ext i k
  simp [mulMat, LinearMap.toMatrixAlgEquiv_apply, Algebra.ofId_apply]

theorem mulMat_comm {F LL V : Type} (C : Type) [Field F] [Field LL] [Algebra F LL] [AddCommGroup V]
    [Module LL V] [Module F V] [IsScalarTower F LL V] [CommRing C] [Algebra F C] {d : ℕ}
    (b : Module.Basis (Fin d) F V) (a : LL) (f : V →ₗ[LL] V) (N : Matrix (Fin d) (Fin d) C)
    (hN : ∀ i k, N i k = algebraMap F C (b.repr (f (b k)) i)) :
    mulMat C b a * N = N * mulMat C b a := by
  have h : N = ((Algebra.ofId F C).mapMatrix.comp (LinearMap.toMatrixAlgEquiv b).toAlgHom)
      (f.restrictScalars F) := by
    ext i k
    simp [hN, LinearMap.toMatrixAlgEquiv_apply, Algebra.ofId_apply]
  rw [h, mulMat, AlgHom.comp_apply, ← map_mul, ← map_mul]
  congr 1
  ext v
  simp

variable {l : ℕ} [Fact l.Prime]

theorem exists_undo (K LL : FinExt l) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) :
    ∃ ι : GQ l, ∀ x : ↥K.1, ι (τ x : Om l) = (x : Om l) := by
  let φ := AlgEquiv.ofBijective (τ.liftNormal (Om l))
    (Algebra.IsAlgebraic.algHom_bijective _)
  refine ⟨φ.symm, fun x => ?_⟩
  rw [AlgEquiv.symm_apply_eq]
  exact (τ.liftNormal_commutes (Om l) x).symm

theorem Ks_mono (K : FinExt l) {s m : ℕ} (hm : s ≤ m) : Ks K s ≤ Ks K m := by
  refine sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ fun x hx => ?_) _
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
  change x ^ (l ^ (s + n)) = 1
  rw [pow_add, pow_mul, show x ^ l ^ s = 1 from hx, one_pow]

theorem rat_mem_subC (F : IntermediateField ℚ_[l] (Om l)) (c : ℚ_[l]) :
    algebraMap ℚ_[l] (PadicComplex l) c ∈ subC F :=
  ⟨algebraMap ℚ_[l] (Om l) c, F.algebraMap_mem c,
    (IsScalarTower.algebraMap_apply ℚ_[l] (Om l) (PadicComplex l) c).symm⟩

theorem finite_jumps (P : LocPrime l) (K LL : FinExt l) (h7K : fontCore (P.PD K))
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) {d : ℕ}
    (b : Module.Basis (Fin d) ℚ_[l] T.V) : {u | IsJumpV (P.PD K) T.ρ τ u}.Finite := by
  let AK : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) := { V := T.V, ρ := T.ρ, cont := T.cont }
  have hK : Module.Finite ↥LL.1 ↥(DdR (P.PD K) T.ρ) :=
    (h7K _ _ (GlobalTheory.LocalIntegers.goodO_integers l LL) AK).2.1.1
  have hanti : ∀ a, FilV (P.PD K) (LL := ↥LL.1) (V := T.V) (a + 1) ≤ FilV (P.PD K) a := by
    obtain ⟨Φ, h1, -⟩ := GlobalTheory.exists_coord_tensor_dR (P.PD K) T.ρ b
    intro a z hz
    exact (h1 a z).2 fun i => (P.PD K).Fil_anti a ((h1 _ z).1 hz i)
  have hE : Module.Finite ↥LL.1 ↥(DdRE (P.PD K) T.ρ τ) :=
    Module.Finite.of_injective (Submodule.inclusion (inf_le_left : DdRE (P.PD K) T.ρ τ ≤ _))
      (Submodule.inclusion_injective _)
  exact GlobalTheory.finite_jumps_inf_filtration _ _ (DdRE (P.PD K) T.ρ τ) (fun a => FilV (P.PD K) a) hE hanti

theorem conj_mem_subC (LL : FinExt l) (F : IntermediateField ℚ_[l] (Om l)) {d : ℕ}
    (B : ↥LL.1 →ₐ[ℚ_[l]] Matrix (Fin d) (Fin d) (PadicComplex l))
    (X Y : Matrix (Fin d) (Fin d) (PadicComplex l))
    (h : ∀ (a : ↥(OL LL)) i j, (X * B a * Y) i j ∈ subC F) (a : ↥LL.1) (i j : Fin d) :
    (X * B a * Y) i j ∈ subC F := by
  haveI := LL.2
  have ha : IsAlgebraic ℤ_[l] a :=
    (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥LL.1).2 (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨c, hc, hint⟩ := ha.exists_integral_multiple
  have hc' : (c : ℚ_[l]) ≠ 0 := fun h0 => hc (Subtype.ext h0)
  have e : a = (c : ℚ_[l])⁻¹ • (c • a) := by
    change a = (c : ℚ_[l])⁻¹ • ((c : ℚ_[l]) • a)
    rw [inv_smul_smul₀ hc']
  have h1 := h ⟨c • a, hint⟩ i j
  rw [e, map_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, Algebra.smul_def]
  exact mul_mem (rat_mem_subC F _) h1

def toC (K : FinExt l) : ↥K.1 →ₐ[ℚ_[l]] PadicComplex l :=
  (IsScalarTower.toAlgHom ℚ_[l] (Om l) (PadicComplex l)).comp K.1.val

theorem toC_apply (K : FinExt l) (x : ↥K.1) : toC K x = ((x : Om l) : PadicComplex l) := rfl

theorem frame_of_dec (P : LocPrime l) (AI : LocAinf l P) (Θ : ThetaL P AI) (K LL : FinExt l)
    (m : ℕ) (hKm : K.1 ≤ Ks K m) (h7K : fontCore (P.PD K))
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
    (hDR : IsDR (P.PD K) T.ρ) {d : ℕ} (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l))
    (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (hM : IsMat K LL T M A)
    (Dm : Matrix (Fin d) (Fin d) (PadicComplex l))
    (U0 : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (g : GQ l)
    (hD : IsDec AI.actC P.χQ K m M Dm U0 g)
    (hA : ∀ a i j, (Dm⁻¹ * A a * Dm) i j ∈ intC (Ks K m)) :
    ∃ (r : ℕ) (Pm : Matrix (Fin r) (Fin d) (PadicComplex l))
      (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l) (J : Finset ℤ),
      (∀ u, u ∈ J → IsJumpV (P.PD K) T.ρ τ u) ∧ {u | IsJumpV (P.PD K) T.ρ τ u}.Finite ∧
      Frame P.χQ K m U g ∧ HTBasis AI.actC P.χQ (Gj K m) U (J : Set ℤ) ∧
      (∀ σ ∈ Gj K m, Pm * M σ = U σ * Pm.map (AI.actC σ)) ∧
      ball l r ⊆ Pm.mulVec '' ball l d ∧
      (∀ x ∈ ball l d, (l : PadicComplex l) • Pm.mulVec x ∈ ball l r) ∧
      ∀ y : Fin d → ℚ_[l],
        Pm.mulVec (fun a => algebraMap ℚ_[l] (PadicComplex l) (y a)) ∈ Pm.mulVec '' ball l d →
        ∀ a, ‖y a‖ ≤ 1 := by
  haveI := K.2
  have ha : IsActC AI.actC := ⟨AI.actC_ext, AI.actC_norm⟩
  obtain ⟨b, hbM, hbA, hbT⟩ := exists_ratBasis_of_isMat l K LL T d M A hM
  obtain ⟨n, α, β, h1, h2⟩ := exists_sep_elem ℚ_[l] ↥K.1
  have hfin := finite_jumps P K LL h7K T τ b
  obtain ⟨B, hB⟩ : ∃ B : ↥LL.1 →ₐ[ℚ_[l]] Matrix (Fin d) (Fin d) (PadicComplex l),
      B = mulMat (PadicComplex l) b := ⟨_, rfl⟩
  have hBe : ∀ a, B a = Matrix.of fun i k =>
      algebraMap ℚ_[l] (PadicComplex l) (b.repr (a • b k) i) := fun a => by rw [hB, mulMat_eq]
  obtain ⟨E, hE⟩ : ∃ E : Matrix (Fin d) (Fin d) (PadicComplex l),
      E = ∑ j, toC K (β j) • B (τ (α j)) := ⟨_, rfl⟩
  have hEE : E * E = E := by
    rw [hE]
    exact sep_idem (B.comp τ) (toC K) α β h1 h2
  have hG : Gj K m ≤ GK K := IntermediateField.fixingSubgroup_le hKm
  have hβ : ∀ x : ↥K.1, toC K x ∈ subC (Ks K m) := fun x => ⟨x, hKm x.2, rfl⟩
  have hEM : ∀ σ ∈ Gj K m, E * M σ = M σ * E := by
    intro σ hσ
    rw [hE, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, hB,
      mulMat_comm _ b _ (T.ρ ⟨σ, hG hσ⟩) (M σ) (hbM ⟨σ, hG hσ⟩)]
  have hEσ : ∀ σ ∈ Gj K m, E.map (AI.actC σ) = E := by
    intro σ hσ
    ext i k
    refine act_fix ha hσ ?_
    rw [hE, Matrix.sum_apply]
    refine sum_mem fun j _ => ?_
    rw [Matrix.smul_apply, smul_eq_mul, hBe]
    exact mul_mem (hβ _) (rat_mem_subC _ _)
  have hEF : ∀ i k, (Dm⁻¹ * E * Dm) i k ∈ subC (Ks K m) := by
    intro i k
    rw [hE, Finset.mul_sum, Finset.sum_mul, Matrix.sum_apply]
    refine sum_mem fun j _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
    refine mul_mem (hβ _) (conj_mem_subC LL _ B _ _ (fun a i k => ?_) _ _ _)
    have : B a = A a := by
      rw [hBe]
      ext i k
      exact (hbA a i k).symm
    rw [this]
    exact (hA a i k).1
  have hDD : Dm * Dm⁻¹ = 1 := Matrix.mul_nonsing_inv _ hD.1
  obtain ⟨r, R, S, hR, hS, hRS, hRe, heSR⟩ := GlobalTheory.exists_integral_factor_of_idempotent_subfield
    (PadicComplex l) (subC (Ks K m)) d (Dm⁻¹ * E * Dm) hEF (by
      calc Dm⁻¹ * E * Dm * (Dm⁻¹ * E * Dm) = Dm⁻¹ * (E * (Dm * Dm⁻¹) * E) * Dm := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hDD, Matrix.mul_one, hEE])
  have ht : IsUnit (P.ιB P.tB) := by
    rw [← P.period_datum_t_eq K]
    exact (P.PD K).t_unit.map _
  obtain ⟨u, y, hy0, hyD, hli, hfix⟩ := GlobalTheory.DeRhamSymbolBasis.exists_symbol_basis l P AI Θ K LL T
    hDR d b M hbM ht.unit ht.unit_spec
  obtain ⟨c1, c2, c3, c4, c5, Q, hQ⟩ := frame_of_idem AI.actC P.χQ ha K m d r M U0 Dm E g hD hEM
    hEσ hEF R S hR hS hRS hRe heSR (fun k i => Θ.θ (y k i)) u hli
    (fun σ hσ k => hfix σ (hG hσ) k) (hfin.toFinset : Set ℤ) (by
      intro k hk
      by_contra hJ
      apply hk
      have := GlobalTheory.EmbeddingJump.proj_eq_zero l P AI Θ K LL T τ d b n α β h1 ht.unit ht.unit_spec
        (u k) (y k) (hy0 k) (hyD k) (by simpa using hJ)
      rw [hE]
      simp only [hBe, toC_apply]
      exact this)
  refine ⟨r, R * Dm⁻¹, _, g, hfin.toFinset, fun u hu => by simpa using hu, hfin, c1, c2, c3, c4, c5,
    ?_⟩
  rintro z ⟨x, hx, hxz⟩
  obtain ⟨ι, hι⟩ := exists_undo K LL τ
  obtain ⟨ρ, Pr, p1, p2, p3⟩ := GlobalTheory.EigenCoord.exists_matrix l K LL T d b hbT ι
  have hPE : Pr * E = Pr := by
    rw [hE, Matrix.mul_sum]
    have : ∀ j, Pr * (toC K (β j) • B (τ (α j))) = toC K (α j * β j) • Pr := by
      intro j
      rw [Matrix.mul_smul, hBe, p2, hι, smul_smul, map_mul, mul_comm, toC_apply K (α j)]
    simp only [this]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.sum_smul, ← map_sum, h2, map_one, one_smul]
  apply p3
  have : Pr.mulVec (fun a => algebraMap ℚ_[l] (PadicComplex l) (z a)) = Pr.mulVec x := by
    have h3 : ∀ v, Pr.mulVec v = Pr.mulVec (Q.mulVec ((R * Dm⁻¹).mulVec v)) := fun v => by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, hQ, hPE]
    rw [h3 x, h3, hxz]
  rw [this]
  exact norm_mulVec_le _ _ p1 hx

theorem exists_tau_frame : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm7 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; ∀ (T : LocLat S.G S.Qp S.LL S.O) (M0 h0 : ℕ) (τ : S.K →ₐ[S.Qp] S.LL), HypW S E T M0 h0 → ∀ (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A → ∃ (r : ℕ) (Pm : Matrix (Fin r) (Fin d) (PadicComplex l)) (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l) (J : Finset ℤ), (∀ u, u ∈ J → IsJumpV S.PD T.ρ τ u) ∧ {u | IsJumpV S.PD T.ρ τ u}.Finite ∧ Frame (D.loc l).χQ K (mN l s (M0 + h0)) U g ∧ HTBasis (D.locA l).actC (D.loc l).χQ (Gj K (mN l s (M0 + h0))) U (J : Set ℤ) ∧ (∀ σ ∈ Gj K (mN l s (M0 + h0)), Pm * M σ = U σ * Pm.map ((D.locA l).actC σ)) ∧ ball l r ⊆ Pm.mulVec '' ball l d ∧ (∀ x ∈ ball l d, (l : PadicComplex l) • Pm.mulVec x ∈ ball l r) ∧ ∀ y : Fin d → ℚ_[l], Pm.mulVec (fun a => algebraMap ℚ_[l] (PadicComplex l) (y a)) ∈ Pm.mulVec '' ball l d → ∀ a, ‖y a‖ ≤ 1 := by
  intro D HW F h7 l _ K s LL h S E T M0 h0 τ hW d M A hM
  obtain ⟨Θ⟩ := GlobalTheory.ThetaTie.nonempty_thetaL D l
  obtain ⟨Dm, U, g, hD, hA⟩ := GlobalTheory.Cyc.Decomp.exists_decompletion D HW F l K s LL h T M0 h0 hW d M A hM
  have hKm : K.1 ≤ Ks K (mN l s (M0 + h0)) :=
    h.2.2.1.trans (Ks_mono K (by unfold mN; omega))
  exact frame_of_dec (D.loc l) (D.locA l) Θ K LL _ hKm (h7 l K) T τ
    (GlobalTheory.Cyc.CrysDeRham.isDR_of_isCrysOn D HW h7 l K s LL h T hW.1) M A hM Dm U g hD hA

end GlobalTheory.TauFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTauComponentFrameOfLatticeStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tau_component_frame_of_lattice : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm7 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; ∀ (T : LocLat S.G S.Qp S.LL S.O) (M0 h0 : ℕ) (τ : S.K →ₐ[S.Qp] S.LL), HypW S E T M0 h0 → ∀ (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A → ∃ (r : ℕ) (Pm : Matrix (Fin r) (Fin d) (PadicComplex l)) (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l) (J : Finset ℤ), (∀ u, u ∈ J → IsJumpV S.PD T.ρ τ u) ∧ {u | IsJumpV S.PD T.ρ τ u}.Finite ∧ Frame (D.loc l).χQ K (mN l s (M0 + h0)) U g ∧ HTBasis (D.locA l).actC (D.loc l).χQ (Gj K (mN l s (M0 + h0))) U (J : Set ℤ) ∧ (∀ σ ∈ Gj K (mN l s (M0 + h0)), Pm * M σ = U σ * Pm.map ((D.locA l).actC σ)) ∧ ball l r ⊆ Pm.mulVec '' ball l d ∧ (∀ x ∈ ball l d, (l : PadicComplex l) • Pm.mulVec x ∈ ball l r) ∧ ∀ y : Fin d → ℚ_[l], Pm.mulVec (fun a => algebraMap ℚ_[l] (PadicComplex l) (y a)) ∈ Pm.mulVec '' ball l d → ∀ a, ‖y a‖ ≤ 1 := by
  first | exact @GlobalTheory.TauFrame.exists_tau_frame | exact GlobalTheory.TauFrame.exists_tau_frame | (intros; apply GlobalTheory.TauFrame.exists_tau_frame <;> assumption)
end
