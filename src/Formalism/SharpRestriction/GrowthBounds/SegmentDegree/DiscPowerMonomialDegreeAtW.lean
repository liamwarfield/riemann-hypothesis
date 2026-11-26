module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DminusLeBeS
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DiscriminantNonzeroModUniformiser
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.FourHundredSixteenLeA

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DiscPowerMonomialMemSupported
section -- merged from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DiscPowerTimesMonomial
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Kit

variable (D : Formalism.BasicNotions.D7) (hV : admB2 D) {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {n : ℕ} [NeZero n] (S : Set ℤ)

include hV

theorem mem_vg_mul {a b : ℤ} {P Q : MvPolynomial (ℤ × Fin n) R} (hP : (a : WithTop ℤ) ≤ valS LZ S P)
    (hQ : (b : WithTop ℤ) ≤ valS LZ S Q) : ((a + b : ℤ) : WithTop ℤ) ≤ valS LZ S (P * Q) := by
  have h := ((hV R ℤ n LZ S).1 P Q).1
  rw [h, WithTop.coe_add]
  exact add_le_add hP hQ

omit hV [IsDomain R] [IsDiscreteValuationRing R] in
theorem mem_vg_C (c : R) : ((0 : ℤ) : WithTop ℤ) ≤ valS LZ S (C c : MvPolynomial (ℤ × Fin n) R) :=
  by
  unfold valS
  refine Finset.le_inf fun k hk => ?_
  have h := sDegs_C (R := R) LZ S (lastIdx n) c k hk
  rw [Set.mem_singleton_iff] at h
  subst h
  exact le_rfl

theorem mem_vg_pow {a : ℤ} {P : MvPolynomial (ℤ × Fin n) R} (hP : (a : WithTop ℤ) ≤ valS LZ S P) (m : ℕ) :
    (((m : ℤ) * a : ℤ) : WithTop ℤ) ≤ valS LZ S (P ^ m) := by
  induction m with
  | zero => simpa using mem_vg_C (R := R) (n := n) S 1
  | succ k ih =>
    have e : (((k + 1 : ℕ) : ℤ) * a : ℤ) = (k : ℤ) * a + a := by push_cast; ring
    rw [e, pow_succ]
    exact mem_vg_mul D hV S ih hP

theorem mem_vg_prod {κ : Type} (s : Finset κ) (f : κ → MvPolynomial (ℤ × Fin n) R) (a : κ → ℤ)
    (h : ∀ i ∈ s, (a i : WithTop ℤ) ≤ valS LZ S (f i)) :
    ((∑ i ∈ s, a i : ℤ) : WithTop ℤ) ≤ valS LZ S (∏ i ∈ s, f i) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using mem_vg_C (R := R) (n := n) S 1
  · intro i s hi ih h
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact mem_vg_mul D hV S (h i (Finset.mem_insert_self i s))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

omit hV [IsDomain R] [IsDiscreteValuationRing R] in
theorem mem_vg_X (v : ℤ × Fin n) (he : Even v.1) :
    ((0 : ℤ) : WithTop ℤ) ≤ valS LZ S (X v : MvPolynomial (ℤ × Fin n) R) := by
  unfold valS
  refine Finset.le_inf fun k hk => ?_
  have hk0 : (0 : ℤ) ≤ k := by
    by_cases hS : v.1 ∈ S
    · have hv : LZ.vec v.1 = true := by simp [LZ, he]
      have h := sDegs_X_vec (R := R) LZ S (lastIdx n) v.1 v.2 hS hv k hk
      have h01 : k = 0 ∨ k = 1 := by simpa using h
      rcases h01 with h | h <;> simp [h]
    · have h := sDegs_X_out (R := R) LZ S (lastIdx n) v hS k hk
      rw [Set.mem_singleton_iff] at h
      simp [h]
  exact WithTop.coe_le_coe.mpr hk0

theorem mem_vg_monom {κ : Type} (s : Finset κ) (v : κ → ℤ × Fin n) (e : κ → ℕ) (he : ∀ i ∈ s, Even (v i).1) :
    ((0 : ℤ) : WithTop ℤ) ≤ valS LZ S (∏ i ∈ s, (X (v i) : MvPolynomial (ℤ × Fin n) R) ^ e i) := by
  have h0 : ∀ i ∈ s, (((fun _ => (0 : ℤ)) i : ℤ) : WithTop ℤ) ≤
      valS LZ S ((X (v i) : MvPolynomial (ℤ × Fin n) R) ^ e i) := by
    intro i hi
    simpa using mem_vg_pow D hV S (mem_vg_X (R := R) S (v i) (he i hi)) (e i)
  simpa using mem_vg_prod D hV S s (fun i => (X (v i) : MvPolynomial (ℤ × Fin n) R) ^ e i) (fun _ => 0) h0

end Kit

namespace Dat

variable {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) (p K : ℕ)

def discPowerTimesMonomial (O : Type) [CommRing O] (j : ℤ) (b : ℤ → ℕ) : MvPolynomial (ℤ × Fin r) O :=
  X.Dw O j ^ X.m0 K *
      (∏ i : Fin r, MvPolynomial.X (X.F.fr (j - 1) i.val, (0 : Fin r)) ^
        ((b (X.F.fr (j - 1) i.val) : ℤ) - X.Bw p K j (X.F.fr (j - 1) i.val)).toNat)


omit [NeZero n'] [NeZero r] in
def memMu (O : Type) [CommRing O] (j : ℤ) (u : Fin r × Fin r → ℕ) : MvPolynomial (ℤ × Fin r) O :=
  ∏ v : Fin r × Fin r, MvPolynomial.X (X.F.fr j v.1.val, v.2) ^ u v

def memPl (O : Type) [CommRing O] (j : ℤ) (μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ) :
    MvPolynomial (ℤ × Fin r) O :=
  segRen X.F j O r (Psi O (plPart μ) (Ican (plPart μ)))

def memA (O : Type) [CommRing O] (j : ℤ) (b : ℤ → ℕ)
    (q : (Fin (segN X.F j + 1) → Fin (r + K) → ℤ) × (ℤ → Finset (Fin K)) × (Fin r × Fin r → ℕ)) :
    MvPolynomial (ℤ × Fin r) O :=
  X.discPowerTimesMonomial p K O j b * X.memMu O j q.2.2 * X.memPl K O j q.1

def memG (O : Type) [CommRing O] (j : ℤ)
    (q : (Fin (segN X.F j + 1) → Fin (r + K) → ℤ) × (ℤ → Finset (Fin K)) × (Fin r × Fin r → ℕ)) :
    MvPolynomial (ℤ × Fin K) O :=
  segRen X.F j O K (Psi O (tanPart q.1) q.2.1)

def memM [NeZero K] (j : ℤ) (μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ) : ℤ → ℤ :=
  Function.extend (segE X.F j)
    (fun i => if Even (segE X.F j i) then tanPart μ i.succ 0 else tanPart μ i.castSucc 0) 0

theorem famEl_eq (O : Type) [CommRing O] (j : ℤ) (b : ℤ → ℕ)
    (q : (Fin (segN X.F j + 1) → Fin (r + K) → ℤ) × (ℤ → Finset (Fin K)) × (Fin r × Fin r → ℕ)) :
    X.famEl p K O j b q = plEmb O r K (X.memA p K O j b q) * nmEmb O r K (X.memG K O j q) := by
  first
  | (simp only [famEl, memA, discPowerTimesMonomial, memMu, memPl, memG, PsiPl, PsiTan, segRen, plEmb, nmEmb, map_mul,
      rename_rename, Function.comp_def, plVar, tanVar]
     ring)
  | (simp only [famEl, memA, discPowerTimesMonomial, memMu, memPl, memG, PsiPl, PsiTan, segRen, plEmb, nmEmb, map_mul,
      rename_rename, Function.comp_def]
     ring_nf)

end Dat

def RestMemA (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.BOK p K j b → ∀ q : X.Idx p K j (X.restr j b),
      X.memA p K O j b q.1 ∈ supported O {v : ℤ × Fin r | v.1 ∈ X.F.letters j} ∧
      X.memG K O j q.1 ∈ supported O {v : ℤ × Fin K | v.1 ∈ X.F.letters j ∧ ¬ X.F.IsW j v.1} ∧
      ∀ x ∈ X.F.letters j, ¬ X.F.IsW j x →
        (Even x → lam1S LZ {y | y ≤ x} (X.memG K O j q.1) ≤ ((X.memM K j q.1.1 x : ℤ) : WithBot ℤ) ∧
            ((X.memM K j q.1.1 x + (X.m0 K : ℤ) : ℤ) : WithTop ℤ) ≤ valS LZ {y | y < x} (X.memA p K O j b q.1)) ∧
        (¬ Even x → lam1S LZ {y | y < x} (X.memG K O j q.1) ≤ ((X.memM K j q.1.1 x : ℤ) : WithBot ℤ) ∧
            ((X.memM K j q.1.1 x + (X.m0 K : ℤ) : ℤ) : WithTop ℤ) ≤ valS LZ {y | y ≤ x} (X.memA p K O j b q.1)) ∧
        geR (valS LZ {y | y < x} (X.memA p K O j b q.1)) (X.thc p K j b x)

def RestMemB (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.BOK p K j b → ∀ q : X.Idx p K j (X.restr j b),
      ∀ mm ∈ (plEmb O r K (X.memA p K O j b q.1) * nmEmb O r K (X.memG K O j q.1)).support,
        ∀ x ∈ X.F.letters j, ¬ X.F.IsW j x → (ordDeg mm x : ℝ) ≤ X.oc p K j x

def RestMemC (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.BOK p K j b → ∀ q : X.Idx p K j (X.restr j b),
      plEmb O r K (X.memA p K O j b q.1) * nmEmb O r K (X.memG K O j q.1) ∈ Pol O (r + K) b

def RestMemD (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.BOK p K j b → ∀ q : X.Idx p K j (X.restr j b),
      plEmb O r K (X.memA p K O j b q.1) * nmEmb O r K (X.memG K O j q.1) ∈ restrictSupport O (X.resSet p K j)

theorem restMem_of_rests (C₀ : ℝ) (hA : RestMemA C₀) (hB : RestMemB C₀) (hC : RestMemC C₀) (hD : RestMemD C₀) :
    RestMem C₀ := by
  intro p n' r K _ _ _ X O _ _ _ hS hX hCLa hCk j b hb q
  have hA' := hA p n' r K X O hS hX hCLa hCk j b hb q
  have hB' := hB p n' r K X O hS hX hCLa hCk j b hb q
  have hC' := hC p n' r K X O hS hX hCLa hCk j b hb q
  have hD' := hD p n' r K X O hS hX hCLa hCk j b hb q
  rw [X.famEl_eq p K O j b q.1]
  simp only [Dat.Mj, XX', Submodule.mem_inf]
  refine ⟨⟨⟨Submodule.subset_span ⟨X.memA p K O j b q.1, X.memG K O j q.1, X.memM K j q.1.1,
    hA'.1, hA'.2.1, hA'.2.2, rfl⟩, ?_⟩, hC'⟩, hD'⟩
  rw [MvPolynomial.mem_restrictSupport_iff]
  intro mm hmm
  exact hB' mm hmm

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem mem_isSt_Ican {N r : ℕ} [NeZero r] {n0 : ℕ} {be : ℤ} {ν : Fin (N + 1) → Fin r → ℤ} (H : PlHyp n0 be ν) :
    IsSt ν (Ican ν) := by
  classical
  have hbe : 0 ≤ be := by
    have := (H.rng N le_rfl 0).1
    rwa [H.fin] at this
  have hlast : ν (Fin.last N) 0 = be := by
    have := H.fin 0
    rw [← stg_eq ν N (by omega)] at this
    exact this
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    rw [Ican_eq H, if_neg]
    intro h
    exact hc (mem_colRange_of_le_entry ν (Fin.last N) 0 (by omega) (by rw [hlast]; exact h.2))
  · intro c
    rw [Ican_eq H, pEnd_eq]
    by_cases h1 : 1 ≤ c
    · rw [if_pos h1]
      by_cases h2 : c ≤ be
      · rw [if_pos ⟨h1, h2⟩, colH_all fun m => by rw [H.fin]; exact h2, Finset.card_univ, Fintype.card_fin]
      · rw [if_neg fun h => h2 h.2, colH_none fun m => by rw [H.fin]; omega, Finset.card_empty]
    · rw [if_neg h1, if_neg fun h => h1 h.1, colH_all fun m => by rw [H.fin]; omega, Finset.card_empty]
      omega
  · intro c t
    unfold tabCol
    by_cases h1 : 1 ≤ c
    · rw [if_pos h1, if_pos (by omega : (1 : ℤ) ≤ c + 1), Ican_eq H, Ican_eq H]
      by_cases h2 : c + 1 ≤ be
      · rw [if_pos ⟨by omega, h2⟩, if_pos ⟨h1, by omega⟩]
      · rw [if_neg fun h => h2 h.2]
        simp
    · rw [if_neg h1]
      have hc0 : Ican ν c = ∅ := by rw [Ican_eq H, if_neg fun h => h1 h.1]
      rw [hc0, Finset.sdiff_empty]
      exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))

section Ctx

variable {p n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] {X : Dat n' r}

theorem exists_path_decomposition (D : Formalism.BasicNotions.D7) (hAdm : AdmB D) (hX : X.Hyp p K) (j : ℤ) (b : ℤ → ℕ)
    (q : X.Idx p K j (X.restr j b)) :
    ∃ (dd b' b'' : Fin (segN X.F j) → ℕ) (P : PPath (r + K) (segN X.F j) (segLL X.F j) dd)
      (P1 : PPath r (segN X.F j) (segLL X.F j) b') (P2 : PPath K (segN X.F j) (segLL X.F j) b''),
      P.mu = q.1.1 ∧ P1.mu = plPart q.1.1 ∧ P2.mu = tanPart q.1.1 ∧ (∀ i, b' i + b'' i = dd i) ∧
      (∀ i, Formalism.MainNotions.CovariantDegrees.CondC (segLL X.F j) (plPart q.1.1) (tanPart q.1.1) i) ∧
      X.IsPATH p K j (X.restr j b) q.1.1 dd ∧ X.IsGood p K j (X.restr j b) q.1.1 ∧
      IsSt (tanPart q.1.1) q.1.2.1 ∧
      (∀ v, q.1.2.2 v + 2 * X.beS p K j (X.restr j b) < X.Qc p K j) ∧
      ∀ (i : Fin (segN X.F j)) (i' : Fin r), segE X.F j i = X.F.fr j i'.val →
        dd i + ∑ c, q.1.2.2 (i', c) = X.restr j b (X.F.fr j i'.val) := by
  obtain ⟨dd, hP, hG, hSt, hu, hd⟩ := q.2
  obtain ⟨P, hPμ⟩ := hP.path
  have hNK : segN X.F j + r ≤ K := le_trans (Nat.add_le_add_right (hX.card j) r) hX.NsK
  have h10 : BracketPolynomialSpan D := hAdm.2.2.2.2.2.2.2.2.2.1
  obtain ⟨b', b'', hsum, ⟨P1, h1⟩, ⟨P2, h2⟩, hC⟩ :=
    (h10 (segN X.F j) r K (segLL X.F j) dd hNK (plPart q.1.1) (tanPart q.1.1)).mp ⟨P, by rw [hPμ, joinPT_parts]⟩
  exact ⟨dd, b', b'', P, P1, P2, hPμ, h1, h2, hsum, hC, hP, hG, hSt, hu, hd⟩

theorem mem_W_vec (hX : X.Hyp p K) (j : ℤ) (l : Fin (segN X.F j)) (hl : l.val < r) :
    (segLL X.F j).vec l = true := by
  have hW : X.F.IsW j (segE X.F j l) := (TE.dict_w hX.valid l).mpr hl
  rw [comb_vec]
  exact comb_W_even X.F j hX.valid _ (segE_mem X.F j l) hW

theorem mem_tan_zero (hX : X.Hyp p K) (j : ℤ) {dd : Fin (segN X.F j) → ℕ}
    (P : PPath (r + K) (segN X.F j) (segLL X.F j) dd) (s : Fin (segN X.F j + 1)) (hs : s.val ≤ r) (c : Fin K) :
    tanPart P.mu s c = 0 := by
  apply le_antisymm
  · exact T.mu_nonpos P s.val s.isLt (Fin.natAdd r c) (by simp only [Fin.val_natAdd]; omega)
  · exact comb_nonneg_of_vec P s (fun l hl => mem_W_vec hX j l (by omega)) _

theorem tangent_degree_zero_at_w (hX : X.Hyp p K) (j : ℤ) {dd b'' : Fin (segN X.F j) → ℕ}
    (P : PPath (r + K) (segN X.F j) (segLL X.F j) dd) (P2 : PPath K (segN X.F j) (segLL X.F j) b'')
    (h2 : P2.mu = tanPart P.mu) (i : Fin (segN X.F j)) (hW : X.F.IsW j (segE X.F j i)) : b'' i = 0 := by
  have hi : i.val < r := (TE.dict_w hX.valid i).mp hW
  have hs := T.step_vec P2 i (mem_W_vec hX j i hi)
  have h3 := hs.2.2
  rw [h2] at h3
  have : ∑ a, (tanPart P.mu i.succ a - tanPart P.mu i.castSucc a) = 0 :=
    Finset.sum_eq_zero fun a _ => by
      rw [mem_tan_zero hX j P i.succ (by simp only [Fin.val_succ]; omega) a,
        mem_tan_zero hX j P i.castSucc (by simp only [Fin.val_castSucc]; omega) a, sub_zero]
  rw [this] at h3
  exact_mod_cast h3.symm

theorem mem_thc_restr (hX : X.Hyp p K) (j : ℤ) (b : ℤ → ℕ) (x : ℤ) (hx : x ∈ X.toLate j) :
    X.thc p K j (X.restr j b) x = X.thc p K j b x := by
  classical
  obtain ⟨ho1, ho2⟩ := oldest_letter_in_segment p n' r K X hX j x hx
  unfold Dat.thc
  split_ifs with hW
  · rfl
  · have hl : X.F.oldest j x ∈ X.toLate j := (mem_late X j _).mpr ⟨ho1, hW⟩
    unfold Dat.restr
    rw [if_pos hl]

theorem mem_det_supported (R : Type) [CommRing R] {n : ℕ} (y : Fin n → ℤ) (s : Set (ℤ × Fin n))
    (h : ∀ a c, (y a, c) ∈ s) :
    Matrix.det (Matrix.of fun a c : Fin n => (MvPolynomial.X (y a, c) : MvPolynomial (ℤ × Fin n) R)) ∈
      supported R s := by
  rw [Matrix.det_apply]
  refine Subalgebra.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  refine Subalgebra.mul_mem _ (intCast_mem _ _) (Subalgebra.prod_mem _ fun i _ => ?_)
  exact Algebra.subset_adjoin ⟨_, h (σ i) i, rfl⟩

theorem disc_power_monomial_mem_supported (O : Type) [CommRing O] (j : ℤ) (b : ℤ → ℕ) (s : Set (ℤ × Fin r))
    (h : ∀ (a c : Fin r), (X.F.fr (j - 1) a.val, c) ∈ s) : X.discPowerTimesMonomial p K O j b ∈ supported O s := by
  have hXm : ∀ v ∈ s, (MvPolynomial.X v : MvPolynomial (ℤ × Fin r) O) ∈ supported O s :=
    fun v hv => Algebra.subset_adjoin ⟨v, hv, rfl⟩
  unfold Dat.discPowerTimesMonomial Dat.Dw
  refine Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (mem_det_supported O _ s h) _)
    (Subalgebra.prod_mem _ fun i _ => Subalgebra.pow_mem _ (hXm _ (h i 0)) _)

theorem mem_Mu_supported (O : Type) [CommRing O] (j : ℤ) (u : Fin r × Fin r → ℕ) (s : Set (ℤ × Fin r))
    (h : ∀ (a c : Fin r), (X.F.fr j a.val, c) ∈ s) : X.memMu O j u ∈ supported O s := by
  have hXm : ∀ v ∈ s, (MvPolynomial.X v : MvPolynomial (ℤ × Fin r) O) ∈ supported O s :=
    fun v hv => Algebra.subset_adjoin ⟨v, hv, rfl⟩
  unfold Dat.memMu
  exact Subalgebra.prod_mem _ fun v _ => Subalgebra.pow_mem _ (hXm _ (h v.1 v.2)) _

theorem mem_vg_A (D : Formalism.BasicNotions.D7) (hB2 : admB2 D) (hX : X.Hyp p K) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (j : ℤ) (b : ℤ → ℕ)
    (q : (Fin (segN X.F j + 1) → Fin (r + K) → ℤ) × (ℤ → Finset (Fin K)) × (Fin r × Fin r → ℕ))
    (S : Set ℤ) (hS : ∀ a : Fin r, X.F.fr (j - 1) a.val ∈ S) (a : ℤ)
    (ha : (a : WithTop ℤ) ≤ valS LZ S (X.memPl K O j q.1)) :
    (((X.m0 K : ℤ) + a : ℤ) : WithTop ℤ) ≤ valS LZ S (X.memA p K O j b q) := by
  have hV := hX.valid
  have hevW : ∀ a : Fin r, Even (X.F.fr (j - 1) a.val) := fun a => (hV.2.2.2.2.1 (j - 1) a.val a.isLt).2
  have hevT : ∀ a : Fin r, Even (X.F.fr j a.val) := fun a => (hV.2.2.2.2.1 j a.val a.isLt).2
  have hD : ((1 : ℤ) : WithTop ℤ) ≤ valS LZ S (X.Dw O j) := by
    unfold Dat.Dw
    rw [(hB2 O ℤ r LZ S).2.2 (fun a => X.F.fr (j - 1) a.val) (fr_injective X.F hV (j - 1))
      (fun a => ⟨hS a, by simp [LZ, hevW a]⟩)]
    exact le_rfl
  have h1 := mem_vg_pow D hB2 S hD (X.m0 K)
  have h2 := mem_vg_monom D hB2 (R := O) S Finset.univ (fun i : Fin r => (X.F.fr (j - 1) i.val, (0 : Fin r)))
    (fun i => ((b (X.F.fr (j - 1) i.val) : ℤ) - X.Bw p K j (X.F.fr (j - 1) i.val)).toNat) (fun i _ => hevW i)
  have h3 := mem_vg_monom D hB2 (R := O) S Finset.univ (fun v : Fin r × Fin r => (X.F.fr j v.1.val, v.2))
    q.2.2 (fun v _ => hevT v.1)
  have h4 := mem_vg_mul D hB2 S (mem_vg_mul D hB2 S (mem_vg_mul D hB2 S h1 h2) h3) ha
  unfold Dat.memA Dat.discPowerTimesMonomial Dat.memMu
  have e : (X.m0 K : ℤ) * 1 + 0 + 0 + a = (X.m0 K : ℤ) + a := by ring
  rw [e] at h4
  exact h4

end Ctx

theorem restMemA_of (D : Formalism.BasicNotions.D7) (hAdm : AdmB D) (C₀ : ℝ) : RestMemA C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S hX hLa hk j b hb q
  classical
  have : Fact p.Prime := ⟨hX.prime⟩
  have hV := hX.valid
  have hB2 : admB2 D := hAdm.2.1
  have hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D := hAdm.2.2.2.2.2.2.2.2.1
  obtain ⟨dd, b', b'', P, P1, P2, hPμ, h1, h2, hsum, hC, hPATH, hGood, hSt, hu, hd⟩ := exists_path_decomposition D hAdm hX j b q
  have stg_castSucc {N r : ℕ} (ν : Fin (N + 1) → Fin r → ℤ) (l : Fin N) : ν l.castSucc = stg ν l.val := by
    unfold stg
    rw [dite_eq_left (by have := l.isLt; omega)]
    rfl
  have stg_succ {N r : ℕ} (ν : Fin (N + 1) → Fin r → ℤ) (l : Fin N) : ν l.succ = stg ν (l.val + 1) := by
    unfold stg
    rw [dite_eq_left (by have := l.isLt; omega)]
    rfl
  have stg_plPart {N r : ℕ} {K : ℕ} (μ : Fin (N + 1) → Fin (r + K) → ℤ) (i : ℕ) (m : Fin r) :
      stg (plPart μ) i m = stg μ i (Fin.castAdd K m) := by
    unfold stg
    split_ifs <;> rfl
  have colH_step {r : ℕ} {ν ν' : Fin r → ℤ} (hν : Antitone ν) (hν' : Antitone ν') (ha : ∀ a, ν a ≤ ν' a)
      (hb : ∀ (a : Fin r) (h : a.val + 1 < r), ν' ⟨a.val + 1, h⟩ ≤ ν a) (c : ℤ) :
      colH ν c ≤ colH ν' c ∧ colH ν' c ≤ colH ν c + 1 := by
    constructor
    · unfold colH
      apply Finset.card_le_card
      intro m hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
      exact le_trans hm (ha m)
    · unfold colH
      set S := Finset.univ.filter fun m => c ≤ ν m with hS
      set S' := Finset.univ.filter fun m => c ≤ ν' m with hS'
      have hsub : S'.image Fin.val ⊆ insert 0 (S.image fun a => a.val + 1) := by
        intro x hx
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, S', S, Finset.mem_insert] at hx ⊢
        obtain ⟨m, hm, rfl⟩ := hx
        rcases Nat.eq_zero_or_pos m.val with h0 | hpos
        · left
          exact h0
        · right
          have hlt : m.val - 1 < r := by omega
          have h1 : (m.val - 1) + 1 < r := by omega
          have hm' : (⟨(m.val - 1) + 1, h1⟩ : Fin r) = m := Fin.ext (by simp; omega)
          refine ⟨⟨m.val - 1, hlt⟩, ?_, by simp; omega⟩
          have h2 := hb ⟨m.val - 1, hlt⟩ h1
          rw [hm'] at h2
          exact le_trans hm h2
      calc S'.card = (S'.image Fin.val).card := (Finset.card_image_of_injective _ Fin.val_injective).symm
        _ ≤ (insert 0 (S.image fun a => a.val + 1)).card := Finset.card_le_card hsub
        _ ≤ (S.image fun a => a.val + 1).card + 1 := Finset.card_insert_le _ _
        _ ≤ S.card + 1 := by
          have := Finset.card_image_le (s := S) (f := fun a : Fin r => a.val + 1)
          omega
  have dplus_le_beS (X : Dat n' r) (p K : ℕ) (hX : X.Hyp p K) (j : ℤ) (b : ℤ → ℕ) (μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ)
      (dd : Fin (segN X.F j) → ℕ) (hP : X.IsPATH p K j b μ dd) (s : ℕ) (hs : s ≤ segN X.F j - r) :
      T.dplus (segLL X.F j) dd s ≤ X.beS p K j b := by
    classical
    have hr : 0 < r := NeZero.pos r
    have hV := hX.valid
    unfold T.dplus Dat.beS
    have himg : (X.F.letters j).filter (· < X.F.fr j 0) =
        (Finset.univ.filter fun l : Fin (segN X.F j) => l.val < segN X.F j - r).image (segE X.F j) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hx, hlt⟩
        obtain ⟨i, rfl⟩ := segE_surj X.F j hx
        exact ⟨i, (segE_lt_fr_iff X.F hV hr j i).mp hlt, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨segE_mem X.F j i, (segE_lt_fr_iff X.F hV hr j i).mpr hi⟩
    rw [himg, Finset.sum_image (fun a _ b _ h => (segE_strictMono X.F j).injective h), Finset.sum_filter]
    refine Finset.sum_le_sum fun l _ => ?_
    split_ifs with h1 h2 h2
    · rw [hP.degs l ((segE_lt_fr_iff X.F hV hr j l).mpr h2)]
    · omega
    · exact Nat.zero_le _
    · exact le_rfl
  have plHyp_of (X : Dat n' r) (p K : ℕ) (hX : X.Hyp p K) (j : ℤ) (b : ℤ → ℕ) (μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ)
      (dd : Fin (segN X.F j) → ℕ) (hP : X.IsPATH p K j b μ dd) :
      PlHyp (segN X.F j - r) (X.beS p K j b : ℤ) (plPart μ) := by
    classical
    have hr : 0 < r := NeZero.pos r
    have hV := hX.valid
    obtain ⟨P, hPμ⟩ := hP.path
    have hrN : r ≤ segN X.F j := k_r_le_segN X.F hV hr j
    have hNK : segN X.F j + r ≤ K := le_trans (Nat.add_le_add_right (hX.card j) r) hX.NsK
  
    have htau : ∀ t (ht : t < r), ∃ l : Fin (segN X.F j), l.val = segN X.F j - r + t ∧
        segE X.F j l = X.F.fr j t ∧ HStrip (stg μ (segN X.F j - r + t)) (stg μ (segN X.F j - r + t + 1)) (dd l) := by
      intro t ht
      let l : Fin (segN X.F j) := ⟨segN X.F j - r + t, by omega⟩
      have hl : segE X.F j l = X.F.fr j t := (segE_eq_fr_iff X.F hV j l ht).mpr rfl
      have hvec : (segLL X.F j).vec l = true := by
        rw [comb_vec, hl]; exact (hV.2.2.2.2.1 j t ht).2
      have hs := T.step_vec P l hvec
      rw [hPμ, stg_castSucc μ, stg_succ μ] at hs
      exact ⟨l, rfl, hl, hs⟩
    have hlow : ∀ i ≤ segN X.F j - r, ∀ m, stg μ i m ≤ (X.beS p K j b : ℤ) := by
      intro i hi m
      have h1 := T.mu_le_dplus P i (by omega) m
      rw [hPμ, stg_eq μ i (by omega)] at h1
      have h2 := dplus_le_beS X p K hX j b μ dd hP i hi
      exact le_trans h1 (by exact_mod_cast h2)
    have hup : ∀ t ≤ r, ∀ m, stg μ (segN X.F j - r + t) m ≤ (X.beS p K j b : ℤ) := by
      intro t
      induction t with
      | zero => intro _ m; exact hlow _ le_rfl m
      | succ t ih =>
        intro ht m
        obtain ⟨l, hlv, hl, hs⟩ := htau t (by omega)
        rw [show segN X.F j - r + (t + 1) = segN X.F j - r + t + 1 by ring]
        by_cases hm : m.val = 0
        · have := hP.head l ⟨t, by omega⟩ hl m (by omega)
          rw [stg_succ μ, hlv] at this
          rw [this]
        · have hm' := m.isLt
          have h2 := hs.2.1 ⟨m.val - 1, by omega⟩ (by simp only []; omega)
          have e : (⟨(⟨m.val - 1, by omega⟩ : Fin (r + K)).val + 1, by simp only []; omega⟩ : Fin (r + K)) = m :=
            Fin.ext (by simp only []; omega)
          rw [e] at h2
          exact le_trans h2 (ih (by omega) _)
    have hdom : ∀ k, k < segN X.F j + 1 → Antitone (stg (plPart μ) k) := by
      intro k hk a a' haa
      rw [stg_plPart, stg_plPart, ← stg_eq μ k hk, ← hPμ]
      exact P.dom _ (by rw [Fin.le_def]; simpa using haa)
    refine ⟨?_, ?_, ?_⟩
    · intro i hi m
      rw [stg_plPart]
      constructor
      · have h1 := T.mu_nonneg P i (by omega) (Fin.castAdd K m) (by
          have := m.isLt
          simp only [Fin.val_castAdd]; omega)
        rwa [hPμ, stg_eq μ i (by omega)] at h1
      · by_cases h : i ≤ segN X.F j - r
        · exact hlow i h _
        · have := hup (i - (segN X.F j - r)) (by omega) (Fin.castAdd K m)
          rwa [show segN X.F j - r + (i - (segN X.F j - r)) = i by omega] at this
    · intro m
      rw [stg_plPart]
      obtain ⟨l, hlv, hl, -⟩ := htau (r - 1) (by omega)
      have := hP.head l ⟨r - 1, by omega⟩ hl (Fin.castAdd K m) (by
        have := m.isLt
        simp only [Fin.val_castAdd]; omega)
      rw [stg_succ μ, hlv, show segN X.F j - r + (r - 1) + 1 = segN X.F j by omega] at this
      exact this
    · intro t ht c
      obtain ⟨l, hlv, hl, hs⟩ := htau t ht
      refine colH_step (hdom _ (by omega)) (hdom _ (by omega)) ?_ ?_ c
      · intro a
        rw [stg_plPart, stg_plPart]
        exact hs.1 _
      · intro a h
        rw [stg_plPart, stg_plPart]
        have := hs.2.1 (Fin.castAdd K a) (by simp only [Fin.val_castAdd]; omega)
        exact this
  have H := plHyp_of X p K hX j _ _ dd hPATH
  have hI' : IsSt P1.mu (Ican P1.mu) := by rw [h1]; exact mem_isSt_Ican H
  have hI'' : IsSt P2.mu q.1.2.1 := by rw [h2]; exact hSt
  have u1 := standard_polynomial_mem_bounds (segLL X.F j) b' (fun th M => (hA3 p O S _ r (segLL X.F j) b' th M).1) P1 _ hI'
  have u2 := standard_polynomial_mem_bounds (segLL X.F j) b'' (fun th M => (hA3 p O S _ K (segLL X.F j) b'' th M).1) P2 _ hI''
  rw [h1] at u1
  rw [h2] at u2
  refine ⟨?_, ?_, ?_⟩
  · unfold Dat.memA
    refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _ ?_ ?_) ?_
    · exact disc_power_monomial_mem_supported O j b _ fun a _ => TE.frp_mem hV j a.val a.isLt
    · exact mem_Mu_supported O j _ _ fun a _ => k_fr_mem_letters X.F hV j a.isLt
    · unfold Dat.memPl
      refine mem_supported.mpr fun v hv => ?_
      obtain ⟨u, _, rfl⟩ := mem_vars_rename _ _ (Finset.mem_coe.mp hv)
      exact segE_mem X.F j u.1
  · unfold Dat.memG
    refine mem_supported.mpr fun v hv => ?_
    obtain ⟨u, hu', rfl⟩ := mem_vars_rename _ _ (Finset.mem_coe.mp hv)
    exact ⟨segE_mem X.F j u.1, fun hW => pol_vars_deg u2.1 hu'
      (tangent_degree_zero_at_w hX j P P2 (by rw [h2, hPμ]) u.1 hW)⟩
  · intro x hx hW
    obtain ⟨i, rfl⟩ := segE_surj X.F j hx
    obtain ⟨sA1, sA2, -, -⟩ := seg_val X.F j (Psi O (plPart q.1.1) (Ican (plPart q.1.1))) i
    obtain ⟨-, -, sG3, sG4⟩ := seg_val X.F j (Psi O (tanPart q.1.1) q.1.2.1) i
    have hxl : segE X.F j i ∈ X.toLate j := (mem_late X j _).mpr ⟨hx, hW⟩
    have hM : X.memM K j q.1.1 (segE X.F j i) =
        (if Even (segE X.F j i) then tanPart q.1.1 i.succ 0 else tanPart q.1.1 i.castSucc 0) :=
      (segE_strictMono X.F j).injective.extend_apply _ _ i
    have hWlt : ∀ a : Fin r, X.F.fr (j - 1) a.val < segE X.F j i := by
      intro a
      have h3 : ¬ segE X.F j i ≤ X.F.fr (j - 1) (r - 1) := hW
      have h4 := kfr_le X.F hV (j - 1) (by have := a.isLt; omega : a.val ≤ r - 1) (by have := a.isLt; omega)
      omega
    have vlt := mem_vg_A D hB2 hX O j b q.1 {y | y < segE X.F j i} hWlt (plPart q.1.1 i.castSucc (lastIdx r))
      (by unfold Dat.memPl; rw [sA2]; exact (u1.2 i.castSucc).1)
    have vle := mem_vg_A D hB2 hX O j b q.1 {y | y ≤ segE X.F j i} (fun a => (hWlt a).le)
      (plPart q.1.1 i.succ (lastIdx r)) (by unfold Dat.memPl; rw [sA1]; exact (u1.2 i.succ).1)
    have hCi := hC i
    unfold Formalism.MainNotions.CovariantDegrees.CondC at hCi
    refine ⟨fun he => ⟨?_, ?_⟩, fun he => ⟨?_, ?_⟩, ?_⟩
    · rw [hM, if_pos he]
      unfold Dat.memG
      rw [sG3]; exact (u2.2 i.succ).2
    · refine le_trans (WithTop.coe_le_coe.mpr ?_) vlt
      rw [hM, if_pos he]
      rw [if_pos ((comb_vec X.F j i).mpr he)] at hCi
      omega
    · rw [hM, if_neg he]
      unfold Dat.memG
      rw [sG4]; exact (u2.2 i.castSucc).2
    · refine le_trans (WithTop.coe_le_coe.mpr ?_) vle
      rw [hM, if_neg he]
      rw [if_neg (fun h => he ((comb_vec X.F j i).mp h))] at hCi
      omega
    · refine geR_of_le vlt ?_
      rw [← mem_thc_restr hX j b _ hxl]
      have := (hGood i hW).1
      push_cast
      have hm : (0 : ℝ) ≤ (X.m0 K : ℝ) := Nat.cast_nonneg _
      linarith

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem mem_degAt_det {R : Type} [CommRing R] {n : ℕ} (y : Fin n → ℤ) (t : ℤ) :
    DegAt t (∑ a : Fin n, if y a = t then 1 else 0)
      (Matrix.det (Matrix.of fun a c : Fin n => (MvPolynomial.X (y a, c) : MvPolynomial (ℤ × Fin n) R))) := by
  classical
  rw [Matrix.det_apply]
  refine degAt_sum _ _ fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  have h1 : (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : MvPolynomial (ℤ × Fin n) R) = C (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R) := by
    simp
  rw [h1]
  refine degAt_C_mul _ ?_
  have h2 := degAt_prod (R := R) (x := t) Finset.univ
    (fun i : Fin n => (MvPolynomial.X (y (σ i), i) : MvPolynomial (ℤ × Fin n) R))
    (fun i => if y (σ i) = t then 1 else 0) (fun i _ => degAt_X (x := t) (y (σ i), i))
  rw [Equiv.sum_comp σ (fun a => if y a = t then 1 else 0)] at h2
  exact h2

namespace Dat

variable {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) (p K : ℕ)

def discPowerMonomialDegree (j : ℤ) (b : ℤ → ℕ) (x : ℤ) : ℕ :=
  X.m0 K * (∑ a : Fin r, if X.F.fr (j - 1) a.val = x then 1 else 0) +
    ∑ i : Fin r, ((b (X.F.fr (j - 1) i.val) : ℤ) - X.Bw p K j (X.F.fr (j - 1) i.val)).toNat *
      (if X.F.fr (j - 1) i.val = x then 1 else 0)


omit [NeZero n'] [NeZero r] in
def memdMu (j : ℤ) (u : Fin r × Fin r → ℕ) (x : ℤ) : ℕ :=
  ∑ v : Fin r × Fin r, u v * (if X.F.fr j v.1.val = x then 1 else 0)

end Dat

section Deg

variable {p n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] {X : Dat n' r}

theorem degAt_disc_power_monomial (O : Type) [CommRing O] (j : ℤ) (b : ℤ → ℕ) (x : ℤ) :
    DegAt x (X.discPowerMonomialDegree p K j b x) (X.discPowerTimesMonomial p K O j b) := by
  classical
  unfold Dat.discPowerMonomialDegree Dat.discPowerTimesMonomial Dat.Dw
  refine degAt_mul (degAt_pow (mem_degAt_det _ x) _) ?_
  exact degAt_prod Finset.univ _ _ fun i _ => degAt_pow (degAt_X (x := x) (X.F.fr (j - 1) i.val, (0 : Fin r))) _

theorem mem_degAt_Mu (O : Type) [CommRing O] (j : ℤ) (u : Fin r × Fin r → ℕ) (x : ℤ) :
    DegAt x (X.memdMu j u x) (X.memMu O j u) := by
  classical
  unfold Dat.memdMu Dat.memMu
  exact degAt_prod Finset.univ _ _ fun v _ => degAt_pow (degAt_X (x := x) (X.F.fr j v.1.val, v.2)) _

theorem disc_power_monomial_degree_off (j : ℤ) (b : ℤ → ℕ) (x : ℤ) (h : ∀ a : Fin r, X.F.fr (j - 1) a.val ≠ x) :
    X.discPowerMonomialDegree p K j b x = 0 := by
  unfold Dat.discPowerMonomialDegree
  simp [h]

theorem mem_dMu_off (j : ℤ) (u : Fin r × Fin r → ℕ) (x : ℤ) (h : ∀ a : Fin r, X.F.fr j a.val ≠ x) :
    X.memdMu j u x = 0 := by
  unfold Dat.memdMu
  simp [h]

theorem disc_power_monomial_degree_at_w (hX : X.Hyp p K) (j : ℤ) (b : ℤ → ℕ) (a0 : Fin r) :
    X.discPowerMonomialDegree p K j b (X.F.fr (j - 1) a0.val) =
      X.m0 K + ((b (X.F.fr (j - 1) a0.val) : ℤ) - X.Bw p K j (X.F.fr (j - 1) a0.val)).toNat := by
  classical
  have hinj := fr_injective X.F hX.valid (j - 1)
  have hiff : ∀ a : Fin r, (X.F.fr (j - 1) a.val = X.F.fr (j - 1) a0.val) ↔ a = a0 :=
    fun a => ⟨fun h => hinj h, fun h => by rw [h]⟩
  unfold Dat.discPowerMonomialDegree
  simp only [hiff]
  simp

theorem mem_dMu_tau (hX : X.Hyp p K) (j : ℤ) (u : Fin r × Fin r → ℕ) (t : Fin r) :
    X.memdMu j u (X.F.fr j t.val) = ∑ c, u (t, c) := by
  classical
  have hinj := fr_injective X.F hX.valid j
  have hiff : ∀ a : Fin r, (X.F.fr j a.val = X.F.fr j t.val) ↔ a = t :=
    fun a => ⟨fun h => hinj h, fun h => by rw [h]⟩
  unfold Dat.memdMu
  rw [Fintype.sum_prod_type]
  simp only [hiff]
  rw [Finset.sum_eq_single t]
  · simp
  · intro a _ ha
    simp [ha]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem mem_degAt_segRen_off {R : Type} [CommRing R] (j : ℤ) {n : ℕ} (A : MvPolynomial (Fin (segN X.F j) × Fin n) R)
    (x : ℤ) (hx : x ∉ X.F.letters j) : DegAt x 0 (segRen X.F j R n A) := by
  refine degAt_of_supported {v : ℤ × Fin n | v.1 ∈ X.F.letters j} ?_ ?_
  · refine mem_supported.mpr fun v hv => ?_
    obtain ⟨u, _, rfl⟩ := mem_vars_rename _ _ (Finset.mem_coe.mp hv)
    exact segE_mem X.F j u.1
  · intro v hv h
    exact hx (h ▸ hv)

end Deg

theorem restMemB_of (D : Formalism.BasicNotions.D7) (hAdm : AdmB D) (C₀ : ℝ) : RestMemB C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S hX hLa hk j b hb q mm hmm x hx hW
  classical
  have : Fact p.Prime := ⟨hX.prime⟩
  have hV := hX.valid
  have hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D := hAdm.2.2.2.2.2.2.2.2.1
  obtain ⟨dd, b', b'', P, P1, P2, hPμ, h1, h2, hsum, hC, hPATH, hGood, hSt, hu, hd⟩ := exists_path_decomposition D hAdm hX j b q
  have H : PlHyp (segN X.F j - r) (X.beS p K j (X.restr j b) : ℤ) (plPart q.1.1) := by
    let μ := q.1.1
    let b := X.restr j b
    have hP : X.IsPATH p K j b μ dd := hPATH
    classical
    have hr : 0 < r := NeZero.pos r
    have hV := hX.valid
    obtain ⟨P, hPμ⟩ := hP.path
    have hrN : r ≤ segN X.F j := k_r_le_segN X.F hV hr j
    have hNK : segN X.F j + r ≤ K := le_trans (Nat.add_le_add_right (hX.card j) r) hX.NsK
  
    have htau : ∀ t (ht : t < r), ∃ l : Fin (segN X.F j), l.val = segN X.F j - r + t ∧
        segE X.F j l = X.F.fr j t ∧ HStrip (stg μ (segN X.F j - r + t)) (stg μ (segN X.F j - r + t + 1)) (dd l) := by
      intro t ht
      let l : Fin (segN X.F j) := ⟨segN X.F j - r + t, by omega⟩
      have hl : segE X.F j l = X.F.fr j t := (segE_eq_fr_iff X.F hV j l ht).mpr rfl
      have hvec : (segLL X.F j).vec l = true := by
        rw [comb_vec, hl]; exact (hV.2.2.2.2.1 j t ht).2
      have hs := T.step_vec P l hvec
      rw [hPμ, stg_castSucc μ, stg_succ μ] at hs
      exact ⟨l, rfl, hl, hs⟩
    have hlow : ∀ i ≤ segN X.F j - r, ∀ m, stg μ i m ≤ (X.beS p K j b : ℤ) := by
      intro i hi m
      have h1 := T.mu_le_dplus P i (by omega) m
      rw [hPμ, stg_eq μ i (by omega)] at h1
      have h2 : T.dplus (segLL X.F j) dd i ≤ X.beS p K j b := by
        let s := i
        have hs : s ≤ segN X.F j - r := hi
        classical
        have hr : 0 < r := NeZero.pos r
        have hV := hX.valid
        unfold T.dplus Dat.beS
        have himg : (X.F.letters j).filter (· < X.F.fr j 0) =
            (Finset.univ.filter fun l : Fin (segN X.F j) => l.val < segN X.F j - r).image (segE X.F j) := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨hx, hlt⟩
            obtain ⟨i, rfl⟩ := segE_surj X.F j hx
            exact ⟨i, (segE_lt_fr_iff X.F hV hr j i).mp hlt, rfl⟩
          · rintro ⟨i, hi, rfl⟩
            exact ⟨segE_mem X.F j i, (segE_lt_fr_iff X.F hV hr j i).mpr hi⟩
        rw [himg, Finset.sum_image (fun a _ b _ h => (segE_strictMono X.F j).injective h), Finset.sum_filter]
        refine Finset.sum_le_sum fun l _ => ?_
        split_ifs with h1 h2 h2
        · rw [hP.degs l ((segE_lt_fr_iff X.F hV hr j l).mpr h2)]
        · omega
        · exact Nat.zero_le _
        · exact le_rfl
      exact le_trans h1 (by exact_mod_cast h2)
    have hup : ∀ t ≤ r, ∀ m, stg μ (segN X.F j - r + t) m ≤ (X.beS p K j b : ℤ) := by
      intro t
      induction t with
      | zero => intro _ m; exact hlow _ le_rfl m
      | succ t ih =>
        intro ht m
        obtain ⟨l, hlv, hl, hs⟩ := htau t (by omega)
        rw [show segN X.F j - r + (t + 1) = segN X.F j - r + t + 1 by ring]
        by_cases hm : m.val = 0
        · have := hP.head l ⟨t, by omega⟩ hl m (by omega)
          rw [stg_succ μ, hlv] at this
          rw [this]
        · have hm' := m.isLt
          have h2 := hs.2.1 ⟨m.val - 1, by omega⟩ (by simp only []; omega)
          have e : (⟨(⟨m.val - 1, by omega⟩ : Fin (r + K)).val + 1, by simp only []; omega⟩ : Fin (r + K)) = m :=
            Fin.ext (by simp only []; omega)
          rw [e] at h2
          exact le_trans h2 (ih (by omega) _)
    have hdom : ∀ k, k < segN X.F j + 1 → Antitone (stg (plPart μ) k) := by
      intro k hk a a' haa
      rw [stg_plPart, stg_plPart, ← stg_eq μ k hk, ← hPμ]
      exact P.dom _ (by rw [Fin.le_def]; simpa using haa)
    refine ⟨?_, ?_, ?_⟩
    · intro i hi m
      rw [stg_plPart]
      constructor
      · have h1 := T.mu_nonneg P i (by omega) (Fin.castAdd K m) (by
          have := m.isLt
          simp only [Fin.val_castAdd]; omega)
        rwa [hPμ, stg_eq μ i (by omega)] at h1
      · by_cases h : i ≤ segN X.F j - r
        · exact hlow i h _
        · have := hup (i - (segN X.F j - r)) (by omega) (Fin.castAdd K m)
          rwa [show segN X.F j - r + (i - (segN X.F j - r)) = i by omega] at this
    · intro m
      rw [stg_plPart]
      obtain ⟨l, hlv, hl, -⟩ := htau (r - 1) (by omega)
      have := hP.head l ⟨r - 1, by omega⟩ hl (Fin.castAdd K m) (by
        have := m.isLt
        simp only [Fin.val_castAdd]; omega)
      rw [stg_succ μ, hlv, show segN X.F j - r + (r - 1) + 1 = segN X.F j by omega] at this
      exact this
    · intro t ht c
      obtain ⟨l, hlv, hl, hs⟩ := htau t ht
      refine colH_step (hdom _ (by omega)) (hdom _ (by omega)) ?_ ?_ c
      · intro a
        rw [stg_plPart, stg_plPart]
        exact hs.1 _
      · intro a h
        rw [stg_plPart, stg_plPart]
        have := hs.2.1 (Fin.castAdd K a) (by simp only [Fin.val_castAdd]; omega)
        exact this
  have hI' : IsSt P1.mu (Ican P1.mu) := by rw [h1]; exact mem_isSt_Ican H
  have hI'' : IsSt P2.mu q.1.2.1 := by rw [h2]; exact hSt
  have u1 := (standard_polynomial_mem_bounds (segLL X.F j) b' (fun th M => (hA3 p O S _ r (segLL X.F j) b' th M).1) P1 _ hI').1
  have u2 := (standard_polynomial_mem_bounds (segLL X.F j) b'' (fun th M => (hA3 p O S _ K (segLL X.F j) b'' th M).1) P2 _ hI'').1
  rw [h1] at u1
  rw [h2] at u2
  obtain ⟨i, rfl⟩ := segE_surj X.F j hx
  have hevW : ∀ a : Fin r, Even (X.F.fr (j - 1) a.val) := fun a => (hV.2.2.2.2.1 (j - 1) a.val a.isLt).2
  have hevT : ∀ a : Fin r, Even (X.F.fr j a.val) := fun a => (hV.2.2.2.2.1 j a.val a.isLt).2
  have hA : ¬ Even (segE X.F j i) → DegAt (segE X.F j i) (0 + 0 + b' i) (X.memA p K O j b q.1) := by
    intro ho
    unfold Dat.memA
    refine degAt_mul (degAt_mul ?_ ?_) (degAt_segRen X.F j u1 i)
    · refine degAt_of_supported {v : ℤ × Fin r | Even v.1} (disc_power_monomial_mem_supported O j b _ fun a _ => hevW a) ?_
      intro v hv h
      exact ho (h ▸ hv)
    · refine degAt_of_supported {v : ℤ × Fin r | Even v.1} (mem_Mu_supported O j _ _ fun a _ => hevT a) ?_
      intro v hv h
      exact ho (h ▸ hv)
  have hG : Even (segE X.F j i) → DegAt (segE X.F j i) (b'' i) (X.memG K O j q.1) := fun _ =>
    degAt_segRen X.F j u2 i
  rw [ordDeg_prod hA hG mm hmm]
  obtain ⟨-, gE, gO⟩ := hGood i hW
  split_ifs with he
  · have hs := (T.step_vec P2 i ((comb_vec X.F j i).mpr he)).2.2
    rw [h2] at hs
    have := gE he
    rw [hs] at this
    exact_mod_cast this
  · have hvec : (segLL X.F j).vec i = false := by
      by_contra h
      exact he ((comb_vec X.F j i).mp (by simpa using h))
    have hs := (T.step_cov P1 i hvec).2.2
    rw [h1] at hs
    have := gO he
    rw [hs] at this
    simpa using this

end Formalism.MainNotions.SelectionLemmas.Pf
