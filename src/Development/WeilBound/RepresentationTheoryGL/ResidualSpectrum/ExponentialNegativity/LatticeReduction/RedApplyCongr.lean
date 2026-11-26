module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.ExpNegGlue

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.LatticeReduction.LatticeHeightZeroEq
noncomputable section

open Matrix Module

namespace PositivityTheory.Rg.Rs.JLatOf

open PositivityTheory.Rg.Rs

variable {k : Type} [Field k] {N : ℕ}

def Mj (k : Type) [Field k] (N j : ℕ) : Submodule k (Fin N → k) where
  carrier := {x | ∀ a : Fin N, (a : ℕ) < j → x a = 0}
  add_mem' := by
    intro x y hx hy a ha
    simp [hx a ha, hy a ha]
  zero_mem' := by
    intro a _
    rfl
  smul_mem' := by
    intro c x hx a ha
    simp [hx a ha]

theorem mem_Mj {j : ℕ} {x : Fin N → k} : x ∈ Mj k N j ↔ ∀ a : Fin N, (a : ℕ) < j → x a = 0 := by
  exact Iff.rfl

theorem Mj_zero : Mj k N 0 = ⊤ := by
  refine eq_top_iff.mpr (fun x _ => ?_)
  intro a ha
  exact absurd ha (Nat.not_lt_zero _)

theorem mem_gmap {g : GL (Fin N) k} {M : Submodule k (Fin N → k)} {y : Fin N → k} :
    y ∈ gmap g M ↔ ∃ x ∈ M, (g : Matrix (Fin N) (Fin N) k) *ᵥ x = y := by
  delta gmap
  simp only [Submodule.mem_map, Matrix.toLin'_apply]

theorem gmap_mul (g h : GL (Fin N) k) (M : Submodule k (Fin N → k)) : gmap (g * h) M = gmap g (gmap h M) := by
  delta gmap
  simp only [Units.val_mul, Matrix.toLin'_mul, Submodule.map_comp]

theorem gmap_one (M : Submodule k (Fin N → k)) : gmap (1 : GL (Fin N) k) M = M := by
  delta gmap
  simp

theorem gmap_inv_mul_eq_iff (g h : GL (Fin N) k) (M : Submodule k (Fin N → k)) :
    gmap (g⁻¹ * h) M = M ↔ gmap h M = gmap g M := by
  constructor
  · intro h1
    conv_rhs => rw [← h1]
    rw [← gmap_mul, mul_inv_cancel_left]
  · intro h1
    rw [gmap_mul, h1, ← gmap_mul, inv_mul_cancel, gmap_one]

theorem finrank_gmap (g : GL (Fin N) k) (M : Submodule k (Fin N → k)) :
    finrank k (gmap g M) = finrank k M := by
  have hinj : Function.Injective (Matrix.toLin' (g : Matrix (Fin N) (Fin N) k)) := by
    intro x y hxy
    have h2 := congrArg (fun v => ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) *ᵥ v) hxy
    simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec] using h2
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj M)).symm

theorem gmap_le_Mj_iff (g : GL (Fin N) k) (j : ℕ) :
    gmap g (Mj k N j) ≤ Mj k N j ↔
      ∀ a b : Fin N, (a : ℕ) < j → j ≤ (b : ℕ) → (g : Matrix (Fin N) (Fin N) k) a b = 0 := by
  constructor
  · intro hle a b ha hb
    have hmem : (Pi.single b 1 : Fin N → k) ∈ Mj k N j := by
      intro a' ha'
      have hne : a' ≠ b := by
        intro he
        rw [he] at ha'
        omega
      simp [Pi.single_apply, hne]
    have h2 := hle (mem_gmap.mpr ⟨_, hmem, rfl⟩) a ha
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h2
  · intro hz y hy
    obtain ⟨x, hx, rfl⟩ := mem_gmap.mp hy
    intro a ha
    show ∑ b : Fin N, (g : Matrix (Fin N) (Fin N) k) a b * x b = 0
    apply Finset.sum_eq_zero
    intro b _
    by_cases hb : (b : ℕ) < j
    · rw [hx b hb, mul_zero]
    · rw [hz a b ha (by omega), zero_mul]

theorem mem_par_iff [Finite k] (g : GL (Fin N) k) (j : ℕ) :
    g ∈ Formalism.UG.P.tjcosets_par N j ↔ gmap g (Mj k N j) = Mj k N j := by
  have hmem : g ∈ Formalism.UG.P.tjcosets_par N j ↔
      ∀ a b : Fin N, (a : ℕ) < j → j ≤ (b : ℕ) → (g : Matrix (Fin N) (Fin N) k) a b = 0 := Iff.rfl
  rw [hmem, ← gmap_le_Mj_iff]
  constructor
  · intro hle
    exact Submodule.eq_of_le_of_finrank_eq hle (finrank_gmap g _)
  · intro heq
    exact heq.le

def ej (N j m : ℕ) (h : m + j = N) (i : Fin m) : Fin N → k := Pi.single (⟨j + i, by omega⟩ : Fin N) 1

theorem linInd_ej (N j m : ℕ) (h : m + j = N) : LinearIndependent k (ej (k := k) N j m h) := by
  have hf : Function.Injective (fun i : Fin m => (⟨j + i, by omega⟩ : Fin N)) := by
    intro a b hab
    simp only [Fin.mk.injEq] at hab
    exact Fin.ext (by omega)
  have h2 := (Pi.basisFun k (Fin N)).linearIndependent.comp _ hf
  convert h2 using 1
  funext i
  simp [ej]

theorem Mj_eq_span (N j m : ℕ) (h : m + j = N) :
    Mj k N j = Submodule.span k (Set.range (ej (k := k) N j m h)) := by
  apply le_antisymm
  · intro x hx
    have hx' : x = ∑ i : Fin m, x ⟨j + i, by omega⟩ • ej (k := k) N j m h i := by
      ext a
      simp only [Finset.sum_apply, Pi.smul_apply, ej, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
      by_cases ha : (a : ℕ) < j
      · rw [hx a ha]
        symm
        apply Finset.sum_eq_zero
        intro i _
        rw [if_neg]
        intro hai
        rw [hai] at ha
        simp at ha
      · rw [Finset.sum_eq_single (⟨(a : ℕ) - j, by omega⟩ : Fin m)]
        · rw [if_pos (Fin.ext (by simp; omega))]
          congr 1
          exact Fin.ext (by simp; omega)
        · intro i _ hi
          rw [if_neg]
          intro hai
          apply hi
          have h3 := congrArg Fin.val hai
          simp at h3
          exact Fin.ext (by simp; omega)
        · intro hne
          exact absurd (Finset.mem_univ _) hne
    rw [hx']
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩ a ha
    have hne : a ≠ ⟨j + i, by omega⟩ := by
      intro he
      rw [he] at ha
      simp at ha
    simp [ej, Pi.single_apply, hne]

theorem finrank_Mj (N j : ℕ) (h : j ≤ N) : finrank k (Mj k N j) = N - j := by
  rw [Mj_eq_span N j (N - j) (by omega), finrank_span_eq_card (linInd_ej N j (N - j) (by omega))]
  simp

theorem gmap_span {ι : Type} (g : GL (Fin N) k) (u : ι → Fin N → k) :
    gmap g (Submodule.span k (Set.range u)) =
      Submodule.span k (Set.range fun i => (g : Matrix (Fin N) (Fin N) k) *ᵥ u i) := by
  delta gmap
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

theorem span_basis_coe {ι : Type} {M : Submodule k (Fin N → k)} (b : Basis ι k M) :
    Submodule.span k (Set.range fun i => (b i : Fin N → k)) = M := by
  have h1 : Set.range (fun i => (b i : Fin N → k)) = M.subtype '' Set.range b := by
    rw [← Set.range_comp]
    rfl
  rw [h1, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]

theorem exists_frame [Finite k] (N j m : ℕ) (h : m + j = N) (u : Fin m → Fin N → k) (hu : LinearIndependent k u) :
    ∃ g : GL (Fin N) k, ∀ i : Fin m, (g : Matrix (Fin N) (Fin N) k) *ᵥ ej N j m h i = u i := by
  subst h
  have hm : m + j - j = m := by omega
  let w : Formalism.UG.P.TjcosetsFr (m + j - j) (m + j) k := fun i => u (Fin.cast hm i)
  have hw : LinearIndependent k w := hu.comp _ (Fin.cast_injective hm)
  obtain ⟨g, hg⟩ := Formalism.UG.P.tjcosets_exists_smul (m + j) j w hw
  refine ⟨g, fun i => ?_⟩
  have h1 := congrFun hg (Fin.cast hm.symm i)
  rw [Formalism.UG.P.GL_smul_standard_tuple] at h1
  have h2 : w (Fin.cast hm.symm i) = u i := by
    simp only [w]
    congr 1
  rw [← h2, ← h1]
  ext a
  (simp [ej, Matrix.mulVec, dotProduct, Pi.single_apply]) <;> rfl

theorem exists_gmap_Mj [Finite k] (M : Submodule k (Fin N → k)) (j : ℕ) (h : finrank k M + j = N) :
    ∃ g : GL (Fin N) k, gmap g (Mj k N j) = M := by
  let b := Module.finBasis k M
  have hli : LinearIndependent k (fun i => (b i : Fin N → k)) :=
    b.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  obtain ⟨g, hg⟩ := exists_frame N j (finrank k M) h (fun i => (b i : Fin N → k)) hli
  refine ⟨g, ?_⟩
  rw [Mj_eq_span N j _ h, gmap_span]
  simp only [hg]
  exact span_basis_coe b

theorem gmap_line (g : GL (Fin N) k) (i₀ : Fin N) (h0 : ∀ a, a ≠ i₀ → (g : Matrix (Fin N) (Fin N) k) a i₀ = 0) :
    gmap g (Submodule.span k {(Pi.single i₀ (1 : k) : Fin N → k)}) =
      Submodule.span k {(Pi.single i₀ (1 : k) : Fin N → k)} := by
  have hcol : (g : Matrix (Fin N) (Fin N) k) *ᵥ Pi.single i₀ 1 =
      (g : Matrix (Fin N) (Fin N) k) i₀ i₀ • (Pi.single i₀ 1 : Fin N → k) := by
    ext a
    by_cases ha : a = i₀
    · subst ha
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    · simp [Matrix.mulVec, dotProduct, Pi.single_apply, ha, h0 a ha]
  have hc : (g : Matrix (Fin N) (Fin N) k) i₀ i₀ ≠ 0 := by
    intro hc
    rw [hc, zero_smul] at hcol
    have hinj : Function.Injective (fun v : Fin N → k => (g : Matrix (Fin N) (Fin N) k) *ᵥ v) := by
      intro x y hxy
      have h2 := congrArg (fun v => ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) *ᵥ v) hxy
      simpa [Matrix.mulVec_mulVec] using h2
    have h3 : (Pi.single i₀ (1 : k) : Fin N → k) = 0 := hinj (by
      show (g : Matrix (Fin N) (Fin N) k) *ᵥ Pi.single i₀ 1 = (g : Matrix (Fin N) (Fin N) k) *ᵥ 0
      rw [hcol, Matrix.mulVec_zero])
    have h4 := congrFun h3 i₀
    simp at h4
  delta gmap
  rw [Submodule.map_span, Set.image_singleton, Matrix.toLin'_apply, hcol,
    Submodule.span_singleton_smul_eq (IsUnit.mk0 _ hc)]

theorem lattice_height_zero_eq (n : ℕ) : H0 k n = Mj k (n + 1) 1 := by
  ext x
  delta H0
  simp only [LinearMap.mem_ker, LinearMap.proj_apply, mem_Mj]
  constructor
  · intro hx a ha
    have ha0 : a = 0 := Fin.ext (Nat.lt_one_iff.mp ha)
    rw [ha0]
    exact hx
  · intro hx
    exact hx 0 (by simp)

theorem stepMat [Finite k] (n : ℕ) (M : Submodule k (Fin (n + 1) → k)) (hM : e0 k n ∈ M) :
    ∃ (jj : Fin (n + 1)) (g : GL (Fin (n + 1)) k), (jj : ℕ) + finrank k M = n + 1 ∧
      gmap g (Mj k (n + 1) jj) = M ∧ gmap g (Mj k (n + 1) (jj + 1)) = M ⊓ H0 k n ∧
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ Pi.single jj 1 = e0 k n ∧
      ∀ b : Fin (n + 1), jj < b → (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) 0 b = 0 := by
  classical
  obtain ⟨r, hr⟩ : ∃ r, r = finrank k M := ⟨_, rfl⟩
  have hr1 : 1 ≤ r := by
    rw [hr, Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    intro hbot
    rw [hbot, Submodule.mem_bot] at hM
    have h5 : (Pi.single (0 : Fin (n + 1)) (1 : k) : Fin (n + 1) → k) 0 = 0 := congrFun hM 0
    simp at h5
  have hrle : r ≤ n + 1 := by
    rw [hr]
    exact (Submodule.finrank_le M).trans (by simp)
  have hH0 : finrank k (H0 k n) = n := by
    rw [lattice_height_zero_eq, finrank_Mj _ _ (by omega)]
    simp
  have hsup : M ⊔ H0 k n = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x = x 0 • e0 k n + (x - x 0 • e0 k n) := by abel
    rw [hx]
    apply Submodule.add_mem_sup (Submodule.smul_mem _ _ hM)
    delta H0 e0
    simp
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq M (H0 k n)
  rw [hsup, finrank_top, Module.finrank_fin_fun, hH0, ← hr] at hdim
  obtain ⟨m, hm⟩ : ∃ m, m = r - 1 := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : Submodule k (Fin (n + 1) → k), P = M ⊓ H0 k n := ⟨_, rfl⟩
  rw [← hP] at hdim
  have hdimMH : finrank k ↥P = m := by omega
  obtain ⟨b⟩ : Nonempty (Basis (Fin m) k ↥P) := ⟨Module.finBasisOfFinrankEq k _ hdimMH⟩
  obtain ⟨v, hv_def⟩ : ∃ v : Fin m → Fin (n + 1) → k, v = fun i => (b i : Fin (n + 1) → k) := ⟨_, rfl⟩
  obtain ⟨u, hu_def⟩ : ∃ u : Fin (m + 1) → Fin (n + 1) → k, u = Fin.cons (e0 k n) v := ⟨_, rfl⟩
  have hvli : LinearIndependent k v := by
    rw [hv_def]
    exact b.linearIndependent.map' P.subtype (Submodule.ker_subtype P)
  have hspanv : Submodule.span k (Set.range v) = M ⊓ H0 k n := by
    rw [hv_def, ← hP]
    exact span_basis_coe b
  have hvmem : ∀ i, v i ∈ M ⊓ H0 k n := by
    intro i
    rw [hv_def, ← hP]
    exact (b i).2
  have he0 : e0 k n ∉ H0 k n := by
    delta H0 e0
    simp
  have hu : LinearIndependent k u := by
    rw [hu_def, linearIndependent_finCons]
    refine ⟨hvli, ?_⟩
    rw [hspanv]
    intro hmem
    exact he0 (Submodule.mem_inf.mp hmem).2
  have hsum : (m + 1) + (n + 1 - r) = n + 1 := by omega
  obtain ⟨g, hg⟩ := exists_frame (n + 1) (n + 1 - r) (m + 1) hsum u hu
  refine ⟨⟨n + 1 - r, by omega⟩, g, by simp only; omega, ?_, ?_, ?_, ?_⟩
  · show gmap g (Mj k (n + 1) (n + 1 - r)) = M
    rw [Mj_eq_span (n + 1) (n + 1 - r) (m + 1) hsum, gmap_span]
    simp only [hg]
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      refine Fin.cases ?_ (fun i => ?_) i
      · rw [hu_def]
        simpa using hM
      · simp only [hu_def, Fin.cons_succ]
        exact (Submodule.mem_inf.mp (hvmem i)).1
    · rw [finrank_span_eq_card hu]
      simp
      omega
  · have hsum' : m + (n + 1 - r + 1) = n + 1 := by omega
    show gmap g (Mj k (n + 1) (n + 1 - r + 1)) = M ⊓ H0 k n
    rw [Mj_eq_span (n + 1) (n + 1 - r + 1) m hsum', gmap_span]
    have hgv : ∀ i : Fin m, (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ ej (n + 1) (n + 1 - r + 1) m hsum' i = v i := by
      intro i
      have hej : ej (k := k) (n + 1) (n + 1 - r + 1) m hsum' i = ej (n + 1) (n + 1 - r) (m + 1) hsum i.succ := by
        simp only [ej]
        congr 1
        ext
        simp
        omega
      rw [hej, hg i.succ, hu_def, Fin.cons_succ]
    simp only [hgv]
    exact hspanv
  · have hej : ej (k := k) (n + 1) (n + 1 - r) (m + 1) hsum 0 = Pi.single ⟨n + 1 - r, by omega⟩ 1 := by
      simp only [ej]
      congr 1
    rw [← hej, hg 0, hu_def]
    rfl
  · intro bb hbb
    have hbb' : n + 1 - r < (bb : ℕ) := hbb
    have hi : (bb : ℕ) - (n + 1 - r + 1) < m := by omega
    let i : Fin m := ⟨(bb : ℕ) - (n + 1 - r + 1), hi⟩
    have hej : ej (k := k) (n + 1) (n + 1 - r) (m + 1) hsum i.succ = Pi.single bb 1 := by
      simp only [ej]
      congr 1
      ext
      simp [i]
      omega
    have h1 := hg i.succ
    rw [hej] at h1
    have h3 : ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ Pi.single bb 1) 0 = (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) 0 bb := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [← h3, h1, hu_def, Fin.cons_succ]
    exact (Submodule.mem_inf.mp (hvmem i)).2

end PositivityTheory.Rg.Rs.JLatOf

end
end

noncomputable section

open NumberField IsDedekindDomain Matrix Module
open Formalism.UG Formalism.UG.P

namespace PositivityTheory.Rg.Rs.JLatOf

open PositivityTheory.Rg.Rs

theorem gmap_Mj_congr {k : Type} [Field k] {N : ℕ} (g g' : GL (Fin N) k) (j : ℕ) (hj : j ≤ N)
    (h : ∀ a b : Fin N, j ≤ (b : ℕ) → (g : Matrix (Fin N) (Fin N) k) a b = (g' : Matrix (Fin N) (Fin N) k) a b) :
    gmap g (Mj k N j) = gmap g' (Mj k N j) := by
  rw [Mj_eq_span N j (N - j) (by omega), gmap_span, gmap_span]
  congr 2
  funext i
  funext a
  simpa [ej, Matrix.mulVec_single_one] using h a ⟨j + i, by omega⟩ (by simp)

theorem rho_eq_of_mk {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (K : Subgroup G) (x : V) (hx : ∀ κ ∈ K, ρ κ x = x) {a b : G}
    (h : (QuotientGroup.mk a : G ⧸ K) = QuotientGroup.mk b) : ρ a x = ρ b x := by
  have hk := QuotientGroup.eq.1 h
  conv_rhs => rw [show b = a * (a⁻¹ * b) by group]
  rw [map_mul, Module.End.mul_apply, hx _ hk]

def dgl {L : Type} [Field L] {N : ℕ} (f : Fin N → L) (hf : ∀ i, f i ≠ 0) : GL (Fin N) L :=
  ⟨diagonal f, diagonal fun i => (f i)⁻¹, by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (hf i), by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (hf i)⟩

theorem dgl_conj_apply {L : Type} [Field L] {N : ℕ} (f h : Fin N → L) (hf : ∀ i, f i ≠ 0) (hh : ∀ i, h i ≠ 0)
    (A : GL (Fin N) L) (a b : Fin N) :
    ((dgl f hf * A * dgl h hh : GL (Fin N) L) : Matrix (Fin N) (Fin N) L) a b = f a * (A : Matrix (Fin N) (Fin N) L) a b * h b := by
  show (diagonal f * (A : Matrix (Fin N) (Fin N) L) * diagonal h) a b = _
  simp [Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem dgl_inv {L : Type} [Field L] {N : ℕ} (f : Fin N → L) (hf : ∀ i, f i ≠ 0) :
    (dgl f hf)⁻¹ = dgl (fun i => (f i)⁻¹) (fun i => inv_ne_zero (hf i)) := by
  ext a b
  rfl

section Loc

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {ϖ : w.adicCompletion E}

abbrev Res (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) : Type :=
  IsLocalRing.ResidueField (Ov E w)

def dd (hϖ : IsUnifV E w ϖ) (N j : ℕ) : GL (Fin N) (w.adicCompletion E) := tjcosets_dG N j ϖ (tjcosets_ne_zero w ϖ hϖ)

theorem dd_val (hϖ : IsUnifV E w ϖ) (N j : ℕ) :
    ((dd hϖ N j : GL (Fin N) (w.adicCompletion E)) : Matrix (Fin N) (Fin N) (w.adicCompletion E)) =
      diagonal fun i : Fin N => if (i : ℕ) < j then ϖ else 1 := rfl

theorem dd_zero (hϖ : IsUnifV E w ϖ) (N : ℕ) : dd hϖ N 0 = 1 := by
  ext a b
  rw [dd_val]
  simp

theorem entry_mem {N : ℕ} (κ : GLint (Fin N) (Ov E w)) (a b : Fin N) :
    ((κ : GL (Fin N) (w.adicCompletion E)) : Matrix (Fin N) (Fin N) (w.adicCompletion E)) a b ∈ Ov E w :=
  ((tjcosets_mem_K_iff (O := Ov E w) N (κ : GL (Fin N) (w.adicCompletion E))).1 κ.2).1 a b

theorem red_eq_zero_iff (hϖ : IsUnifV E w ϖ) {N : ℕ} (κ : GLint (Fin N) (Ov E w)) (a b : Fin N) :
    ((tjcosets_red (Ov E w) N κ : GL (Fin N) (Res E w)) : Matrix (Fin N) (Fin N) (Res E w)) a b = 0 ↔
      ϖ⁻¹ * ((κ : GL (Fin N) (w.adicCompletion E)) : Matrix (Fin N) (Fin N) (w.adicCompletion E)) a b ∈ Ov E w := by
  obtain ⟨g, rfl⟩ := (tjcosets_iso N (Ov E w)).surjective κ
  rw [tjcosets_red_iso, tjcosets_bc_apply, tjcosets_iso_coe, tjcosets_bc_apply]
  exact (tjcosets_hmax w ϖ hϖ _).symm

theorem red_apply_congr {N : ℕ} (κ κ' : GLint (Fin N) (Ov E w)) (a b : Fin N)
    (h : ((κ : GL (Fin N) (w.adicCompletion E)) : Matrix (Fin N) (Fin N) (w.adicCompletion E)) a b =
      ((κ' : GL (Fin N) (w.adicCompletion E)) : Matrix (Fin N) (Fin N) (w.adicCompletion E)) a b) :
    ((tjcosets_red (Ov E w) N κ : GL (Fin N) (Res E w)) : Matrix (Fin N) (Fin N) (Res E w)) a b =
      ((tjcosets_red (Ov E w) N κ' : GL (Fin N) (Res E w)) : Matrix (Fin N) (Fin N) (Res E w)) a b := by
  obtain ⟨g, rfl⟩ := (tjcosets_iso N (Ov E w)).surjective κ
  obtain ⟨g', rfl⟩ := (tjcosets_iso N (Ov E w)).surjective κ'
  rw [tjcosets_red_iso, tjcosets_red_iso, tjcosets_bc_apply, tjcosets_bc_apply]
  rw [tjcosets_iso_coe, tjcosets_iso_coe, tjcosets_bc_apply, tjcosets_bc_apply] at h
  congr 1
  exact Subtype.ext h

theorem mk_eq_iff (hϖ : IsUnifV E w ϖ) {N : ℕ} (j : ℕ) (γ γ' : GLint (Fin N) (Ov E w)) :
    (QuotientGroup.mk ((γ : GL (Fin N) (w.adicCompletion E)) * dd hϖ N j) :
        GL (Fin N) (w.adicCompletion E) ⧸ GLint (Fin N) (Ov E w)) =
      QuotientGroup.mk ((γ' : GL (Fin N) (w.adicCompletion E)) * dd hϖ N j) ↔
    gmap (tjcosets_red (Ov E w) N γ) (Mj (Res E w) N j) = gmap (tjcosets_red (Ov E w) N γ') (Mj (Res E w) N j) := by
  have := tjcosets_finite w
  have hst := tjcosets_stab (O := Ov E w) N j ϖ (GlobalTheory.LFun.mem_Ov_of_isUnifV hϖ) (tjcosets_ne_zero w ϖ hϖ)
    (tjcosets_hmax w ϖ hϖ)
  have h1 : γ'⁻¹ * γ ∈ MulAction.stabilizer (GLint (Fin N) (Ov E w))
      (QuotientGroup.mk (dd hϖ N j) : GL (Fin N) (w.adicCompletion E) ⧸ GLint (Fin N) (Ov E w)) ↔
      gmap (tjcosets_red (Ov E w) N γ) (Mj (Res E w) N j) = gmap (tjcosets_red (Ov E w) N γ') (Mj (Res E w) N j) := by
    rw [dd, hst, Subgroup.mem_comap, mem_par_iff, map_mul, map_inv, gmap_inv_mul_eq_iff]
  rw [← h1, MulAction.mem_stabilizer_iff]
  show _ ↔ (QuotientGroup.mk (((γ'⁻¹ * γ : GLint (Fin N) (Ov E w)) : GL (Fin N) (w.adicCompletion E)) * dd hϖ N j) :
      GL (Fin N) (w.adicCompletion E) ⧸ GLint (Fin N) (Ov E w)) = QuotientGroup.mk (dd hϖ N j)
  rw [QuotientGroup.eq, QuotientGroup.eq]
  have e : ((γ : GL (Fin N) (w.adicCompletion E)) * dd hϖ N j)⁻¹ * ((γ' : GL (Fin N) (w.adicCompletion E)) * dd hϖ N j) =
      (((γ'⁻¹ * γ : GLint (Fin N) (Ov E w)) : GL (Fin N) (w.adicCompletion E)) * dd hϖ N j)⁻¹ * dd hϖ N j := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e]


open Classical in
def vv (hϖ : IsUnifV E w ϖ) {V : Type} [AddCommGroup V] [Module ℂ V] (N : ℕ)
    (ρ : Representation ℂ (GL (Fin N) (w.adicCompletion E)) V) (x : V) (M : Submodule (Res E w) (Fin N → Res E w)) : V :=
  if h : ∃ γ : GLint (Fin N) (Ov E w), gmap (tjcosets_red (Ov E w) N γ) (Mj (Res E w) N (N - finrank (Res E w) M)) = M
  then ρ ((h.choose : GL (Fin N) (w.adicCompletion E)) * dd hϖ N (N - finrank (Res E w) M)) x else 0

theorem vv_eq (hϖ : IsUnifV E w ϖ) {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ}
    (ρ : Representation ℂ (GL (Fin N) (w.adicCompletion E)) V) (x : V)
    (hx : ∀ κ ∈ GLint (Fin N) (Ov E w), ρ κ x = x) {j : ℕ} (hj : j ≤ N) (γ : GLint (Fin N) (Ov E w))
    (M : Submodule (Res E w) (Fin N → Res E w)) (h : gmap (tjcosets_red (Ov E w) N γ) (Mj (Res E w) N j) = M) :
    vv hϖ N ρ x M = ρ ((γ : GL (Fin N) (w.adicCompletion E)) * dd hϖ N j) x := by
  have hf : finrank (Res E w) M = N - j := by rw [← h, finrank_gmap, finrank_Mj N j hj]
  have hj' : N - finrank (Res E w) M = j := by omega
  unfold vv
  split_ifs with hh
  · have hc := hh.choose_spec
    generalize hh.choose = γ0 at hc ⊢
    rw [hj'] at hc ⊢
    exact rho_eq_of_mk ρ _ x hx ((mk_eq_iff hϖ j γ0 γ).2 (hc.trans h.symm))
  · exact absurd ⟨γ, by rw [hj']; exact h⟩ hh

theorem vv_exists (w : HeightOneSpectrum (𝓞 E)) {N : ℕ} (M : Submodule (Res E w) (Fin N → Res E w)) :
    ∃ γ : GLint (Fin N) (Ov E w), gmap (tjcosets_red (Ov E w) N γ) (Mj (Res E w) N (N - finrank (Res E w) M)) = M := by
  have := tjcosets_finite w
  have hle : finrank (Res E w) M ≤ N := (Submodule.finrank_le M).trans (by simp)
  obtain ⟨g, hg⟩ := exists_gmap_Mj M (N - finrank (Res E w) M) (by omega)
  obtain ⟨γ, rfl⟩ := tjcosets_red_surjective (Ov E w) N g
  exact ⟨γ, hg⟩

theorem vv_top (hϖ : IsUnifV E w ϖ) {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ}
    (ρ : Representation ℂ (GL (Fin N) (w.adicCompletion E)) V) (x : V)
    (hx : ∀ κ ∈ GLint (Fin N) (Ov E w), ρ κ x = x) : vv hϖ N ρ x ⊤ = x := by
  rw [vv_eq hϖ ρ x hx (Nat.zero_le N) 1 ⊤ (by rw [map_one, gmap_one, Mj_zero]), dd_zero]
  simp

theorem vv_equiv (hϖ : IsUnifV E w ϖ) {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ}
    (ρ : Representation ℂ (GL (Fin N) (w.adicCompletion E)) V) (x : V)
    (hx : ∀ κ ∈ GLint (Fin N) (Ov E w), ρ κ x = x) (δ : GLint (Fin N) (Ov E w))
    (M : Submodule (Res E w) (Fin N → Res E w)) :
    ρ (δ : GL (Fin N) (w.adicCompletion E)) (vv hϖ N ρ x M) = vv hϖ N ρ x (gmap (tjcosets_red (Ov E w) N δ) M) := by
  obtain ⟨γ, hγ⟩ := vv_exists w M
  have hle : finrank (Res E w) M ≤ N := (Submodule.finrank_le M).trans (by simp)
  have hj : N - finrank (Res E w) M ≤ N := Nat.sub_le _ _
  rw [vv_eq hϖ ρ x hx hj γ M hγ, vv_eq hϖ ρ x hx hj (δ * γ) _ (by rw [map_mul, gmap_mul, hγ])]
  rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_mul, mul_assoc]

theorem fix_conj (hϖ : IsUnifV E w ϖ) (n : ℕ) (γ : GLint (Fin (n + 1)) (Ov E w))
    (hγ : gmap (tjcosets_red (Ov E w) (n + 1) γ) (H0 (Res E w) n) = H0 (Res E w) n) :
    ∃ γ' : GLint (Fin (n + 1)) (Ov E w),
      (γ : GL (Fin (n + 1)) (w.adicCompletion E)) * dd hϖ (n + 1) 1 = dd hϖ (n + 1) 1 * γ' ∧
      gmap (tjcosets_red (Ov E w) (n + 1) γ') (Submodule.span (Res E w) {e0 (Res E w) n}) =
        Submodule.span (Res E w) {e0 (Res E w) n} := by
  have := tjcosets_finite w
  have hϖ0 := tjcosets_ne_zero w ϖ hϖ
  have hst := tjcosets_stab (O := Ov E w) (n + 1) 1 ϖ (GlobalTheory.LFun.mem_Ov_of_isUnifV hϖ) hϖ0 (tjcosets_hmax w ϖ hϖ)
  rw [lattice_height_zero_eq] at hγ
  have h1 := (mem_par_iff _ _).2 hγ
  have h2 : γ ∈ MulAction.stabilizer (GLint (Fin (n + 1)) (Ov E w))
      (QuotientGroup.mk (dd hϖ (n + 1) 1) : GL (Fin (n + 1)) (w.adicCompletion E) ⧸ GLint (Fin (n + 1)) (Ov E w)) := by
    rw [dd, hst]
    exact h1
  rw [MulAction.mem_stabilizer_iff] at h2
  have h3 : (QuotientGroup.mk ((γ : GL (Fin (n + 1)) (w.adicCompletion E)) * dd hϖ (n + 1) 1) :
      GL (Fin (n + 1)) (w.adicCompletion E) ⧸ GLint (Fin (n + 1)) (Ov E w)) = QuotientGroup.mk (dd hϖ (n + 1) 1) := h2
  have h4 := QuotientGroup.eq.1 h3
  set d := dd hϖ (n + 1) 1 with hd
  have hc : d⁻¹ * (γ : GL (Fin (n + 1)) (w.adicCompletion E)) * d ∈ GLint (Fin (n + 1)) (Ov E w) := by
    have e : d⁻¹ * (γ : GL (Fin (n + 1)) (w.adicCompletion E)) * d = (((γ : GL (Fin (n + 1)) (w.adicCompletion E)) * d)⁻¹ * d)⁻¹ := by
      group
    rw [e]
    exact inv_mem h4
  refine ⟨⟨_, hc⟩, by simp only; group, ?_⟩
  apply gmap_line _ 0
  intro a ha
  rw [red_eq_zero_iff hϖ]
  show ϖ⁻¹ * ((d⁻¹ * (γ : GL (Fin (n + 1)) (w.adicCompletion E)) * d : GL (Fin (n + 1)) (w.adicCompletion E)) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) (w.adicCompletion E)) a 0 ∈ Ov E w
  rw [hd, dd, tjcosets_conj_apply]
  have ha' : ¬ (a : ℕ) < 1 := fun h => ha (Fin.ext (by rw [Fin.val_zero]; omega))
  rw [if_neg ha', if_pos (by simp), one_mul, mul_comm _ ϖ, ← mul_assoc, inv_mul_cancel₀ hϖ0, one_mul]
  exact entry_mem γ a 0

theorem step_coset (hϖ : IsUnifV E w ϖ) (n : ℕ) (jj : Fin (n + 1)) (γ : GLint (Fin (n + 1)) (Ov E w))
    (h1 : ∀ a : Fin (n + 1), a ≠ 0 → ((tjcosets_red (Ov E w) (n + 1) γ : GL (Fin (n + 1)) (Res E w)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (Res E w)) a jj = 0)
    (h2 : ∀ a : Fin (n + 1), a ≠ jj → ((tjcosets_red (Ov E w) (n + 1) γ⁻¹ : GL (Fin (n + 1)) (Res E w)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (Res E w)) a 0 = 0)
    (h3 : ∀ b : Fin (n + 1), jj < b → ((tjcosets_red (Ov E w) (n + 1) γ : GL (Fin (n + 1)) (Res E w)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (Res E w)) 0 b = 0) :
    ∃ γ' : GLint (Fin (n + 1)) (Ov E w),
      dd hϖ (n + 1) 1 * ((γ : GL (Fin (n + 1)) (w.adicCompletion E)) * dd hϖ (n + 1) jj) =
        (γ' : GL (Fin (n + 1)) (w.adicCompletion E)) * dd hϖ (n + 1) (jj + 1) ∧
      gmap (tjcosets_red (Ov E w) (n + 1) γ') (Mj (Res E w) (n + 1) (jj + 1)) =
        gmap (tjcosets_red (Ov E w) (n + 1) γ) (Mj (Res E w) (n + 1) (jj + 1)) := by
  have hϖ0 := tjcosets_ne_zero w ϖ hϖ
  have hϖO := GlobalTheory.LFun.mem_Ov_of_isUnifV hϖ
  have hconj : ∀ c : w.adicCompletion E, ϖ * c * ϖ⁻¹ = c := fun c => by
    rw [mul_comm ϖ c, mul_assoc, mul_inv_cancel₀ hϖ0, mul_one]
  have hjj := jj.isLt
  set G := (γ : GL (Fin (n + 1)) (w.adicCompletion E)) with hG
  let f1 : Fin (n + 1) → w.adicCompletion E := fun i => if (i : ℕ) < 1 then ϖ else 1
  let fj : Fin (n + 1) → w.adicCompletion E := fun i => if i = jj then ϖ⁻¹ else 1
  have hf1 : ∀ i, f1 i ≠ 0 := fun i => by
    simp only [f1]
    split_ifs <;> simp [hϖ0]
  have hfj : ∀ i, fj i ≠ 0 := fun i => by
    simp only [fj]
    split_ifs <;> simp [hϖ0]
  set U := dgl f1 hf1 * G * dgl fj hfj with hU
  have hUe : ∀ a b, (U : Matrix (Fin (n + 1)) (Fin (n + 1)) (w.adicCompletion E)) a b =
      f1 a * (G : Matrix (Fin (n + 1)) (Fin (n + 1)) (w.adicCompletion E)) a b * fj b :=
    fun a b => dgl_conj_apply _ _ _ _ _ a b
  have hUi : U⁻¹ = dgl (fun i => (fj i)⁻¹) (fun i => inv_ne_zero (hfj i)) * G⁻¹ *
      dgl (fun i => (f1 i)⁻¹) (fun i => inv_ne_zero (hf1 i)) := by
    rw [hU, _root_.mul_inv_rev, _root_.mul_inv_rev, dgl_inv, dgl_inv, mul_assoc]
  have hUie : ∀ a b, ((U⁻¹ : GL (Fin (n + 1)) (w.adicCompletion E)) : Matrix (Fin (n + 1)) (Fin (n + 1)) (w.adicCompletion E)) a b =
      (fj a)⁻¹ * ((G⁻¹ : GL (Fin (n + 1)) (w.adicCompletion E)) : Matrix (Fin (n + 1)) (Fin (n + 1)) (w.adicCompletion E)) a b *
        (f1 b)⁻¹ := by
    intro a b
    rw [hUi]
    exact dgl_conj_apply _ _ _ _ _ a b
  have hGi : G⁻¹ = ((γ⁻¹ : GLint (Fin (n + 1)) (Ov E w)) : GL (Fin (n + 1)) (w.adicCompletion E)) := by
    rw [hG, Subgroup.coe_inv]
  have hU_mem : U ∈ GLint (Fin (n + 1)) (Ov E w) := by
    rw [tjcosets_mem_K_iff]
    refine ⟨fun a b => ?_, fun a b => ?_⟩
    · rw [hUe]
      simp only [f1, fj]
      by_cases hb : b = jj
      · subst hb
        rw [if_pos rfl]
        by_cases ha : (a : ℕ) < 1
        · rw [if_pos ha, hconj]
          exact entry_mem γ a b
        · rw [if_neg ha, one_mul, mul_comm]
          exact (red_eq_zero_iff hϖ γ a b).1 (h1 a (fun e => ha (by rw [e, Fin.val_zero]; omega)))
      · rw [if_neg hb, mul_one]
        split_ifs
        · exact (Ov E w).mul_mem hϖO (entry_mem γ a b)
        · rw [one_mul]
          exact entry_mem γ a b
    · rw [hUie, hGi]
      simp only [f1, fj]
      by_cases hb : (b : ℕ) < 1
      · rw [if_pos hb]
        have hb0 : b = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
        subst hb0
        by_cases ha : a = jj
        · rw [if_pos ha, inv_inv, hconj]
          exact entry_mem γ⁻¹ a 0
        · rw [if_neg ha, inv_one, one_mul, mul_comm]
          exact (red_eq_zero_iff hϖ γ⁻¹ a 0).1 (h2 a ha)
      · rw [if_neg hb, inv_one, mul_one]
        split_ifs
        · rw [inv_inv]
          exact (Ov E w).mul_mem hϖO (entry_mem γ⁻¹ a b)
        · rw [inv_one, one_mul]
          exact entry_mem γ⁻¹ a b
  refine ⟨⟨U, hU_mem⟩, ?_, ?_⟩
  · apply Units.ext
    show ((dd hϖ (n + 1) 1 : GL (Fin (n + 1)) (w.adicCompletion E)) : Matrix (Fin (n + 1)) (Fin (n + 1)) (w.adicCompletion E)) *
        ((G : Matrix (Fin (n + 1)) (Fin (n + 1)) (w.adicCompletion E)) *
          ((dd hϖ (n + 1) jj : GL (Fin (n + 1)) (w.adicCompletion E)) : Matrix (Fin (n + 1)) (Fin (n + 1)) (w.adicCompletion E))) =
      (diagonal f1 * (G : Matrix (Fin (n + 1)) (Fin (n + 1)) (w.adicCompletion E)) * diagonal fj) *
        ((dd hϖ (n + 1) (jj + 1) : GL (Fin (n + 1)) (w.adicCompletion E)) : Matrix (Fin (n + 1)) (Fin (n + 1)) (w.adicCompletion E))
    rw [dd_val, dd_val, dd_val, Matrix.mul_assoc (diagonal f1 * _), diagonal_mul_diagonal, Matrix.mul_assoc]
    have hdiag : (fun i : Fin (n + 1) => if (i : ℕ) < (jj : ℕ) then ϖ else 1) =
        fun i => fj i * (if (i : ℕ) < (jj : ℕ) + 1 then ϖ else 1) := by
      funext i
      simp only [fj]
      split_ifs <;> first
        | (exfalso; simp only [Fin.ext_iff] at *; omega)
        | simp [hϖ0]
    rw [hdiag]
  · apply gmap_Mj_congr _ _ _ (by omega)
    intro a b hb
    have hb' : jj < b := by
      rw [Fin.lt_def]
      omega
    have hbj : b ≠ jj := fun e => by rw [e] at hb'; exact lt_irrefl _ hb'
    by_cases ha : a = 0
    · subst ha
      rw [h3 b hb', red_eq_zero_iff hϖ]
      show ϖ⁻¹ * (U : Matrix (Fin (n + 1)) (Fin (n + 1)) (w.adicCompletion E)) 0 b ∈ Ov E w
      rw [hUe]
      simp only [f1, fj]
      rw [if_pos (by simp), if_neg hbj, mul_one, ← mul_assoc, inv_mul_cancel₀ hϖ0, one_mul]
      exact entry_mem γ 0 b
    · apply red_apply_congr
      show (U : Matrix (Fin (n + 1)) (Fin (n + 1)) (w.adicCompletion E)) a b = _
      rw [hUe]
      simp only [f1, fj]
      rw [if_neg (fun h => ha (Fin.ext (by rw [Fin.val_zero]; omega))), if_neg hbj, one_mul, mul_one]

open Classical in
theorem Tj_apply (hϖ : IsUnifV E w ϖ) {N : ℕ} (j : ℕ) (g : GL (Fin N) (w.adicCompletion E)) :
    Tj ℂ N (Ov E w) ϖ j g =
      if ∃ a ∈ GLint (Fin N) (Ov E w), ∃ b ∈ GLint (Fin N) (Ov E w), g = a * dd hϖ N j * b then 1 else 0 := by
  unfold Tj
  rw [Set.indicator_apply]
  split_ifs with h1 h2 h2
  · rfl
  · exfalso
    obtain ⟨a, ha, b, hb, h⟩ := h1
    exact h2 ⟨a, ha, b, hb, Units.ext (by rw [Units.val_mul, Units.val_mul]; exact h)⟩
  · exfalso
    obtain ⟨a, ha, b, hb, rfl⟩ := h2
    exact h1 ⟨a, ha, b, hb, by rw [Units.val_mul, Units.val_mul]; rfl⟩
  · rfl


open Classical in
theorem hecke_eq_sum (hϖ : IsUnifV E w ϖ) {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ}
    (ρ : Representation ℂ (GL (Fin N) (w.adicCompletion E)) V) (x : V)
    (hx : ∀ κ ∈ GLint (Fin N) (Ov E w), ρ κ x = x) (j : ℕ) (hj : j ≤ N) :
    GlobalTheory.LFun.heckeVec ρ (GlobalTheory.LFun.KGL w (n := N)) (Tj ℂ N (Ov E w) ϖ j) x =
      ∑ᶠ (M : Submodule (Res E w) (Fin N → Res E w)) (_ : finrank (Res E w) M + j = N), vv hϖ N ρ x M := by
  set K := GLint (Fin N) (Ov E w) with hK
  set T : Set (GL (Fin N) (w.adicCompletion E) ⧸ K) :=
    {c | ∃ a ∈ K, ∃ b ∈ K, c.out = a * dd hϖ N j * b} with hT
  have hA : GlobalTheory.LFun.heckeVec ρ K (Tj ℂ N (Ov E w) ϖ j) x = ∑ᶠ c ∈ T, ρ c.out x := by
    rw [GlobalTheory.LFun.heckeVec, finsum_mem_def]
    congr 1
    funext c
    rw [Tj_apply hϖ j, Set.indicator_apply]
    split_ifs with h1 h2 h2
    · rw [one_smul]
    · exact absurd h1 h2
    · exact absurd h2 h1
    · rw [zero_smul]
  rw [hA]
  let γM : Submodule (Res E w) (Fin N → Res E w) → K := fun M => (vv_exists w M).choose
  have hγM : ∀ M, gmap (tjcosets_red (Ov E w) N (γM M)) (Mj (Res E w) N (N - finrank (Res E w) M)) = M :=
    fun M => (vv_exists w M).choose_spec
  have hs : ∀ M : Submodule (Res E w) (Fin N → Res E w), finrank (Res E w) M + j = N →
      gmap (tjcosets_red (Ov E w) N (γM M)) (Mj (Res E w) N j) = M := by
    intro M hM
    have := hγM M
    rwa [show N - finrank (Res E w) M = j by omega] at this
  let e : Submodule (Res E w) (Fin N → Res E w) → GL (Fin N) (w.adicCompletion E) ⧸ K :=
    fun M => QuotientGroup.mk (((γM M) : GL (Fin N) (w.adicCompletion E)) * dd hϖ N j)
  symm
  refine finsum_mem_eq_of_bijOn (s := {M : Submodule (Res E w) (Fin N → Res E w) | finrank (Res E w) M + j = N})
    (t := T) e ⟨?_, ?_, ?_⟩ ?_
  · intro M _
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K (((γM M) : GL (Fin N) (w.adicCompletion E)) * dd hϖ N j)
    exact ⟨_, (γM M).2, _, h.2, hh⟩
  · intro M hM M' hM' hMM
    exact (hs M hM).symm.trans (((mk_eq_iff hϖ j _ _).1 hMM).trans (hs M' hM'))
  · rintro c ⟨a, ha, b, hb, hc⟩
    have hM : finrank (Res E w) (gmap (tjcosets_red (Ov E w) N ⟨a, ha⟩) (Mj (Res E w) N j)) + j = N := by
      rw [finrank_gmap, finrank_Mj N j hj]
      omega
    refine ⟨gmap (tjcosets_red (Ov E w) N ⟨a, ha⟩) (Mj (Res E w) N j), hM, ?_⟩
    show QuotientGroup.mk _ = c
    rw [(mk_eq_iff hϖ j _ ⟨a, ha⟩).2 (hs _ hM), ← QuotientGroup.out_eq' c, hc, QuotientGroup.eq]
    show (a * dd hϖ N j)⁻¹ * (a * dd hϖ N j * b) ∈ K
    have e2 : (a * dd hϖ N j)⁻¹ * (a * dd hϖ N j * b) = b := by group
    rw [e2]
    exact hb
  · intro M hM
    show vv hϖ N ρ x M = ρ (e M).out x
    rw [vv_eq hϖ ρ x hx hj (γM M) M (hs M hM)]
    exact rho_eq_of_mk ρ K x hx (QuotientGroup.out_eq' (e M)).symm

end Loc

end PositivityTheory.Rg.Rs.JLatOf

namespace PositivityTheory.Rg.Rs

open JLatOf

theorem latOf_holds : LatOf := by
  intro E _ _ w n V _ _ ρ B x S hherm hpos hinv hS
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LFun.exists_isUnifV w
  have := tjcosets_finite w
  letI : Fintype (Res E w) := Fintype.ofFinite _
  have hx : ∀ κ ∈ GLint (Fin (n + 1)) (Ov E w), ρ κ x = x := fun κ hκ => GlobalTheory.LGrp.mem_fixed.1 hS.2.1 κ hκ
  have hcard : Fintype.card (Res E w) = Ideal.absNorm w.asIdeal := by
    rw [Fintype.card_eq_nat_card]
    exact tjcosets_card_residue w
  refine ⟨Res E w, inferInstance, inferInstance, GLint (Fin (n + 1)) (Ov E w), inferInstance,
    tjcosets_red (Ov E w) (n + 1), ρ.comp (GLint (Fin (n + 1)) (Ov E w)).subtype, ρ (dd hϖ (n + 1) 1),
    vv hϖ (n + 1) ρ x, hcard, ?_, ?_⟩
  · refine
      { herm := hherm
        pos := hpos
        surj := tjcosets_red_surjective _ _
        unit := fun γ y z => hinv _ y z
        isom := fun y z => hinv _ y z
        ne := by rw [vv_top hϖ ρ x hx]; exact hS.1
        equiv := fun γ M => vv_equiv hϖ ρ x hx γ M
        fix := ?_
        step := ?_ }
    · intro y hy γ hγ
      obtain ⟨γ', e1, e2⟩ := fix_conj hϖ n γ hγ
      have h := hy γ' e2
      show ρ (γ : GL (Fin (n + 1)) (w.adicCompletion E)) (ρ (dd hϖ (n + 1) 1) y) = ρ (dd hϖ (n + 1) 1) y
      rw [← Module.End.mul_apply, ← map_mul, e1, map_mul, Module.End.mul_apply]
      exact congrArg (ρ (dd hϖ (n + 1) 1)) h
    · intro M hM
      obtain ⟨jj, g, hjj, hg1, hg2, hg3, hg4⟩ := stepMat n M hM
      obtain ⟨γ, rfl⟩ := tjcosets_red_surjective (Ov E w) (n + 1) g
      have h1 : ∀ a : Fin (n + 1), a ≠ 0 → ((tjcosets_red (Ov E w) (n + 1) γ : GL (Fin (n + 1)) (Res E w)) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) (Res E w)) a jj = 0 := by
        intro a ha
        have := congrFun hg3 a
        simpa [Matrix.mulVec_single_one, e0, Pi.single_apply, ha] using this
      have h2 : ∀ a : Fin (n + 1), a ≠ jj → ((tjcosets_red (Ov E w) (n + 1) γ⁻¹ : GL (Fin (n + 1)) (Res E w)) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) (Res E w)) a 0 = 0 := by
        intro a ha
        have e : ((tjcosets_red (Ov E w) (n + 1) γ⁻¹ : GL (Fin (n + 1)) (Res E w)) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) (Res E w)) *ᵥ e0 (Res E w) n = Pi.single jj 1 := by
          rw [← hg3, Matrix.mulVec_mulVec, map_inv, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
        have := congrFun e a
        simpa [Matrix.mulVec_single_one, e0, Pi.single_apply, ha] using this
      obtain ⟨γ', e1, e2⟩ := step_coset hϖ n jj γ h1 h2 hg4
      have hle : (jj : ℕ) + 1 ≤ n + 1 := jj.isLt
      show ρ (dd hϖ (n + 1) 1) (vv hϖ (n + 1) ρ x M) = vv hϖ (n + 1) ρ x (M ⊓ H0 (Res E w) n)
      rw [vv_eq hϖ ρ x hx jj.isLt.le γ M hg1, vv_eq hϖ ρ x hx hle γ' _ (e2.trans hg2), ← Module.End.mul_apply,
        ← map_mul, e1]
  · refine ⟨by simp [hS.2.2.1], fun j hj => ?_⟩
    rw [vv_top hϖ ρ x hx, ← hecke_eq_sum hϖ ρ x hx j hj, hS.2.2.2 ϖ hϖ j hj]
    congr 1
    unfold GlobalTheory.LFun.satEig
    rw [hcard]
    rfl

end PositivityTheory.Rg.Rs

end
