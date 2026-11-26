module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOfMemSB
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenNormalisedSubgroupSubset
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IwahoriDoubleCosets
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCompBlocks

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiUnipotentEqProdRootExchange
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiUnipotentEqProdRootExchange
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

namespace GlobalTheory.RootEx.FJUnipotent
open GlobalTheory.RootEx.Radical

section
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

def midLev (ρ : ℕ) : n ⊕ Fin c → ℕ :=
  Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1))

def midGroup (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) :
    Subgroup (GL (n ⊕ Fin c) k) where
  carrier := {g | Uni (midLev ρ) g.val}
  one_mem' := fun _ _ _ => rfl
  mul_mem' := fun hx hy => Uni.mul hx hy
  inv_mem' := fun hx => Uni.inv hx

theorem NFJ_le_midGroup (ρ : ℕ) : NFJ k n c ρ ≤ midGroup k n c ρ := by
  have key : ∀ p, p = ρ ∨ p = ρ + 1 → N k n c p ≤ midGroup k n c ρ := by
    rintro p hp g hg
    have hg' := (mem_N_iff g).1 hg
    show Uni (midLev ρ) g.val
    intro r s hrs
    apply hg' r s
    rcases r with r | i <;> rcases s with s | j <;>
      simp only [lev, midLev, Sum.elim_inl, Sum.elim_inr] at hrs ⊢ <;> omega
  exact sup_le (key ρ (Or.inl rfl)) (key (ρ + 1) (Or.inr rfl))

theorem exists_col (P : Fin c) {g : GL (n ⊕ Fin c) k} (hg : g ∈ midGroup k n c P.val) :
    ∃ u ∈ N k n c (P.val + 1), ∃ β : n → k, g = u * colE c (P.val + 1) β := by
  have hg' : ∀ r s, midLev (n := n) (c := c) P.val s ≤ midLev P.val r →
      g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s := hg
  refine ⟨g * colE c (P.val + 1) (-fun r => g.val (Sum.inl r) (Sum.inr P)), ?_,
    fun r => g.val (Sum.inl r) (Sum.inr P), ?_⟩
  · rw [mem_N_iff]
    intro r s hrs
    rw [Units.val_mul]
    rcases s with s | j
    · rw [GlobalTheory.RootEx.Exchange.mul_colE_inl]
      apply hg'
      rcases r with r | i <;>
        simp only [lev, midLev, Sum.elim_inl, Sum.elim_inr] at hrs ⊢ <;> omega
    · rw [GlobalTheory.RootEx.Exchange.mul_colE_inr]
      by_cases hj : j = P
      · have hc : j.val + 1 = P.val + 1 := by rw [hj]
        rw [if_pos hc, hj]
        rcases r with r | i
        · have hX : ∀ t, g.val (Sum.inl r) (Sum.inl t) = if r = t then 1 else 0 := by
            intro t
            rw [hg' _ _ (by simp only [midLev, Sum.elim_inl]; omega)]
            simp [Matrix.one_apply]
          simp [hX]
        · have hi : P.val ≤ i.val := by
            rw [hj] at hrs
            simp only [lev, Sum.elim_inr] at hrs
            omega
          have h1 := hg' (Sum.inr i) (Sum.inr P) (by simp only [midLev, Sum.elim_inr]; omega)
          have h2 : ∀ t, g.val (Sum.inr i) (Sum.inl t) = 0 := fun t => by
            rw [hg' _ _ (by simp only [midLev, Sum.elim_inl, Sum.elim_inr]; omega)]
            simp
          simp [h1, h2]
      · have hj' : j.val ≠ P.val := fun h => hj (Fin.ext h)
        have hc : ¬ (j.val + 1 = P.val + 1) := fun h => hj' (by omega)
        rw [if_neg hc, add_zero]
        apply hg'
        rcases r with r | i <;>
          simp only [lev, midLev, Sum.elim_inl, Sum.elim_inr] at hrs ⊢ <;> omega
  · rw [mul_assoc, GlobalTheory.RootEx.Exchange.colE_neg_mul, mul_one]

end

theorem fj_unipotent : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c), (∀ g, g ∈ NFJ k n c ρ ↔ ∃ x ∈ N k n c ρ, ∃ y ∈ N k n c (ρ + 1), g = x * y) ∧ (∀ g : GL (n ⊕ Fin c) k, g ∈ NFJ k n c ρ ↔ ∀ r s : n ⊕ Fin c, Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) s ≤ Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) r → g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s) ∧ ∀ g ∈ NFJ k n c ρ, ∃ u ∈ N k n c (ρ + 1), ∃ β : n → k, g = u * colE c (ρ + 1) β := by
  intro k _ n _ _ c ρ _ hρc
  have hle := NFJ_le_midGroup (k := k) (n := n) (c := c) ρ
  have hcol : ∀ g ∈ NFJ k n c ρ, ∃ u ∈ N k n c (ρ + 1), ∃ β : n → k,
      g = u * colE c (ρ + 1) β :=
    fun g hg => exists_col ⟨ρ, hρc⟩ (hle hg)
  have hcolN : ∀ β : n → k, colE c (ρ + 1) β ∈ N k n c ρ :=
    fun β => colE_mem β (Nat.lt_succ_self ρ)
  have hmid : ∀ g : GL (n ⊕ Fin c) k, g ∈ midGroup k n c ρ → g ∈ NFJ k n c ρ := by
    intro g hg
    obtain ⟨u, hu, β, rfl⟩ := exists_col (k := k) ⟨ρ, hρc⟩ hg
    exact (NFJ k n c ρ).mul_mem (le_sup_right (a := N k n c ρ) hu)
      (le_sup_left (b := N k n c (ρ + 1)) (hcolN β))
  refine ⟨fun g => ⟨fun hg => ?_, ?_⟩, fun g => ⟨fun hg => hle hg, fun hg => hmid g hg⟩, hcol⟩
  · obtain ⟨u, hu, β, hg'⟩ := hcol g⁻¹ ((NFJ k n c ρ).inv_mem hg)
    refine ⟨(colE c (ρ + 1) β)⁻¹, (N k n c ρ).inv_mem (hcolN β), u⁻¹,
      (N k n c (ρ + 1)).inv_mem hu, ?_⟩
    rw [← _root_.mul_inv_rev, ← hg', inv_inv]
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact (NFJ k n c ρ).mul_mem (le_sup_left (b := N k n c (ρ + 1)) hx)
      (le_sup_right (a := N k n c ρ) hy)

end GlobalTheory.RootEx.FJUnipotent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiUnipotentEqProdRootExchangeStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobiUnipotent_eq_prod_rootExchange : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c), (∀ g, g ∈ NFJ k n c ρ ↔ ∃ x ∈ N k n c ρ, ∃ y ∈ N k n c (ρ + 1), g = x * y) ∧ (∀ g : GL (n ⊕ Fin c) k, g ∈ NFJ k n c ρ ↔ ∀ r s : n ⊕ Fin c, Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) s ≤ Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) r → g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s) ∧ ∀ g ∈ NFJ k n c ρ, ∃ u ∈ N k n c (ρ + 1), ∃ β : n → k, g = u * colE c (ρ + 1) β := by
  first | exact @GlobalTheory.RootEx.FJUnipotent.fj_unipotent | exact GlobalTheory.RootEx.FJUnipotent.fj_unipotent | (intros; apply GlobalTheory.RootEx.FJUnipotent.fj_unipotent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationDivZpowOrd
noncomputable section

open GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel Matrix

namespace GlobalTheory.LocalCartan

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]

theorem _root_.GlobalTheory.LocalCartan.diagT_mem_KO {t : n → kˣ} (ht : ∀ i, valuation k (t i : k) = 1) :
    _root_.GlobalTheory.SmGL.diagT k n t ∈ _root_.GlobalTheory.SplitWeil.KO k n := by
  rw [_root_.GlobalTheory.SplitFlip.mem_KO_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [_root_.GlobalTheory.SmGL.val_diagT, diagonal_apply]
    split_ifs with h
    · subst h
      exact (Valuation.mem_integer_iff _ _).mpr (ht i).le
    · exact zero_mem _
  · rw [← map_inv, _root_.GlobalTheory.SmGL.val_diagT, diagonal_apply]
    split_ifs with h
    · subst h
      refine (Valuation.mem_integer_iff _ _).mpr (le_of_eq ?_)
      rw [Pi.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, ht i, inv_one]
    · exact zero_mem _

theorem _root_.GlobalTheory.LocalCartan.exists_diagT (g : GL n k) :
    ∃ x ∈ _root_.GlobalTheory.SplitWeil.KO k n, ∃ y ∈ _root_.GlobalTheory.SplitWeil.KO k n,
      ∃ t : n → kˣ, g = x * _root_.GlobalTheory.SmGL.diagT k n t * y := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors 𝒪[k])
    (Finset.univ : Finset (n × n)) (fun p => (g : Matrix n n k) p.1 p.2)
  choose G hG using fun i j => RingHom.mem_rangeS.mp (hb (i, j) (Finset.mem_univ _))
  set f := algebraMap 𝒪[k] k with hf
  set c : k := f b with hc_def
  have hc : c ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have hGg : f.mapMatrix (Matrix.of G) = c • (g : Matrix n n k) := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply,
      smul_eq_mul]
    rw [hG i j, Algebra.smul_def]
  have hdet : (Matrix.of G).det ≠ 0 := by
    intro h0
    have h1 := congrArg f h0
    rw [RingHom.map_det, hGg, map_zero, Matrix.det_smul] at h1
    exact mul_ne_zero (pow_ne_zero _ hc) ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero h1
  obtain ⟨P, C, hP, hC, a, ha, hPC⟩ := _root_.Formalism.UG.P.cartan_smith (Matrix.of G) hdet
  have hinj : Function.Injective f := IsFractionRing.injective _ _
  have hmap : ∀ A : GL n 𝒪[k],
      ((GeneralLinearGroup.map f A : GL n k) : Matrix n n k) = f.mapMatrix (A : Matrix n n 𝒪[k]) :=
    fun A => by ext i j; rw [GeneralLinearGroup.map_apply]; rfl
  have hmem : ∀ A : GL n 𝒪[k], GeneralLinearGroup.map f A ∈ _root_.GlobalTheory.SplitWeil.KO k n :=
    fun A => by unfold _root_.GlobalTheory.SplitWeil.KO; exact ⟨A, rfl⟩
  have hne : ∀ i, f (a i) / c ≠ 0 := fun i =>
    div_ne_zero ((map_ne_zero_iff f hinj).mpr (ha i)) hc
  refine ⟨_, hmem (GeneralLinearGroup.mk'' P hP), _, hmem (GeneralLinearGroup.mk'' C hC),
    fun i => Units.mk0 (f (a i) / c) (hne i), ?_⟩
  have key : f.mapMatrix P * diagonal (fun i => f (a i)) * f.mapMatrix C = c • (g : Matrix n n k) := by
    have hd : f.mapMatrix (diagonal a) = diagonal (fun i => f (a i)) := by
      rw [RingHom.mapMatrix_apply]
      exact Matrix.diagonal_map (map_zero f)
    rw [← hGg, hPC, map_mul, map_mul, hd]
  have hdiag : diagonal (fun i => ((Units.mk0 (f (a i) / c) (hne i) : kˣ) : k)) =
      c⁻¹ • diagonal (fun i => f (a i)) := by
    ext i j
    by_cases h : i = j <;> simp [diagonal_apply, h, div_eq_inv_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hmap, hmap, _root_.GlobalTheory.SmGL.val_diagT]
  change (g : Matrix n n k) = f.mapMatrix P * _ * f.mapMatrix C
  rw [hdiag, Matrix.mul_smul, Matrix.smul_mul, key, smul_smul, inv_mul_cancel₀ hc, one_smul]

private lemma ord_one_twisted_operators : _root_.GlobalTheory.SmGL.ord k 1 = 0 :=
  _root_.GlobalTheory.SmGL.ord_eq_zero_iff.mpr (by simp)

private lemma ord_inv_twisted_operators (y : kˣ) :
    _root_.GlobalTheory.SmGL.ord k y⁻¹ = -_root_.GlobalTheory.SmGL.ord k y := by
  have h := _root_.GlobalTheory.SmGL.ord_mul k y y⁻¹
  rw [mul_inv_cancel, ord_one_twisted_operators] at h
  omega

private lemma ord_zpow_uniformizer' {ϖ : kˣ}
    (hϖ : valuation k (ϖ : k) = uniformizer k) (m : ℤ) :
    _root_.GlobalTheory.SmGL.ord k (ϖ ^ m) = m := by
  have h1 := _root_.GlobalTheory.SmGL.ord_eq_one hϖ
  induction m using Int.induction_on with
  | zero => simpa using ord_one_twisted_operators
  | succ i ih => rw [_root_.zpow_add_one, _root_.GlobalTheory.SmGL.ord_mul, ih, h1]
  | pred i ih =>
    rw [_root_.zpow_sub_one, _root_.GlobalTheory.SmGL.ord_mul, ih, ord_inv_twisted_operators, h1]
    ring

private lemma exists_unit_mul_zpow_uniformizer {ϖ : kˣ}
    (hϖ : valuation k (ϖ : k) = uniformizer k) (x : kˣ) :
    ∃ u : kˣ, ∃ m : ℤ, valuation k (u : k) = 1 ∧ x = u * ϖ ^ m := by
  refine ⟨x * (ϖ ^ _root_.GlobalTheory.SmGL.ord k x)⁻¹, _root_.GlobalTheory.SmGL.ord k x, ?_, by simp⟩
  apply _root_.GlobalTheory.SmGL.ord_eq_zero_iff.mp
  rw [_root_.GlobalTheory.SmGL.ord_mul, ord_inv_twisted_operators,
    ord_zpow_uniformizer' hϖ]
  ring

theorem _root_.GlobalTheory.LocalCartan.cartan_decomposition (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n]
    (ϖ : kˣ) (g : GL n k) (hϖ : valuation k (ϖ : k) = uniformizer k) :
    ∃ x ∈ _root_.GlobalTheory.SplitWeil.KO k n, ∃ y ∈ _root_.GlobalTheory.SplitWeil.KO k n,
      ∃ m : n → ℤ, g = x * _root_.GlobalTheory.SmGL.diagT k n (fun i => ϖ ^ m i) * y := by
  obtain ⟨x, hx, y, hy, t, rfl⟩ := _root_.GlobalTheory.LocalCartan.exists_diagT g
  choose u m hu htu using fun i => exists_unit_mul_zpow_uniformizer hϖ (t i)
  refine ⟨x * _root_.GlobalTheory.SmGL.diagT k n u,
    mul_mem hx (_root_.GlobalTheory.LocalCartan.diagT_mem_KO hu), y, hy, m, ?_⟩
  have ht : t = u * fun i => ϖ ^ m i := funext htu
  rw [ht, map_mul]
  simp only [mul_assoc]

end GlobalTheory.LocalCartan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLeCard
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound

namespace GlobalTheory.SatakeBound.Rep

section Abstract

variable {G X V : Type} [Group G] [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]

theorem norm_le_card {ι : Type} {π : Representation ℂ G V} (hπ : IsUnitarisable π) {v : V} (hv : v ≠ 0)
    (S : Finset ι) (g : ι → G) (l : ℂ) (h : ∑ c ∈ S, π (g c) v = l • v) : ‖l‖ ≤ S.card := by
  obtain ⟨B, b1, b2, b3⟩ := hπ
  letI : InnerProductSpace.Core ℂ V := UnitInd.core B b1 b2
  letI : NormedAddCommGroup V := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore _
  have hn : ∀ x : G, ‖π x v‖ = ‖v‖ := fun x => by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ) v]
    exact congrArg (fun z : ℂ => √(RCLike.re z)) (b3 x v v)
  have h1 : ‖l‖ * ‖v‖ ≤ S.card * ‖v‖ := by
    rw [← norm_smul, ← h]
    refine (norm_sum_le _ _).trans ?_
    simp [hn]
  exact le_of_mul_le_mul_right h1 (norm_pos_iff.2 hv)

theorem sum_fixed (ρ : Representation ℂ G X) (K : Subgroup G) {w : X} (hw : ∀ x ∈ K, ρ x w = w)
    (S : Finset (G ⧸ K)) (hS : ∀ x ∈ K, ∀ c ∈ S, x • c ∈ S) (x : G) (hx : x ∈ K) :
    ρ x (∑ c ∈ S, ρ c.out w) = ∑ c ∈ S, ρ c.out w := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_nbij' (fun c => x • c) (fun c => x⁻¹ • c) (hS x hx) (hS _ (inv_mem hx))
    (fun c _ => by simp) (fun c _ => by simp) fun c _ => ?_
  have h1 : x • c = ((x * c.out : G) : G ⧸ K) := by
    conv_lhs => rw [← QuotientGroup.out_eq' c]
    rfl
  obtain ⟨y, hy⟩ := QuotientGroup.mk_out_eq_mul K (x * c.out)
  rw [h1, hy, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hw y y.2]

theorem exists_vector [TopologicalSpace G] [IsTopologicalGroup G] {ρ : Representation ℂ G X}
    {π : Representation ℂ G V} (hρ : IsSmooth ρ) (hπ : IsUnitarisable π) {K : Subgroup G}
    (hK : IsCompact (K : Set G)) (f : ρ.IntertwiningMap π) (hf : Function.Surjective f)
    (hs : fixed π K ≠ ⊥) (E : X →ₗ[ℂ] ℂ) (hE : ∀ u : X, (∀ x ∈ K, ρ x u = u) → E u = 0 → u = 0) :
    ∃ w : X, (∀ x ∈ K, ρ x w = w) ∧ E w = 1 ∧ ∀ S : Finset (G ⧸ K), (∀ x ∈ K, ∀ c ∈ S, x • c ∈ S) →
      ‖∑ c ∈ S, E (ρ c.out w)‖ ≤ S.card := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hs
  obtain ⟨u, rfl⟩ := hf v
  obtain ⟨w, hw, hfw⟩ := IwahoriOnto.exists_fixed_map_eq hρ hK f.toLinearMap u fun h hh => by
    show f (ρ h u) = f u
    rw [f.isIntertwining]
    simpa using hv ⟨h, hh⟩
  have hw' : ∀ x ∈ K, ρ x w = w := fun x hx => by simpa using hw ⟨x, hx⟩
  have hfw0 : f w ≠ 0 := fun h => hv0 (hfw.symm.trans h)
  have hEw : E w ≠ 0 := fun h => hfw0 (by rw [hE w hw' h, map_zero])
  obtain ⟨z, hz, hEz, hfz⟩ : ∃ z : X, (∀ x ∈ K, ρ x z = z) ∧ E z = 1 ∧ f z ≠ 0 :=
    ⟨(E w)⁻¹ • w, fun x hx => by rw [map_smul, hw' x hx], by simp [hEw], by
      rw [map_smul]; exact smul_ne_zero (inv_ne_zero hEw) hfw0⟩
  refine ⟨z, hz, hEz, fun S hS => norm_le_card hπ hfz S (fun c => c.out) _ ?_⟩
  have h1 := hE (∑ c ∈ S, ρ c.out z - (∑ c ∈ S, E (ρ c.out z)) • z)
    (fun x hx => by rw [map_sub, sum_fixed ρ K hz S hS x hx, map_smul, hz x hx])
    (by rw [map_sub, map_sum, map_smul, hEz, smul_eq_mul, mul_one, sub_self])
  have h2 := congrArg f (sub_eq_zero.1 h1)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_smul] at h2
  rw [← h2]
  exact Finset.sum_congr rfl fun c _ => (f.isIntertwining _ _ _ _).symm

end Abstract

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem law (α : Fin n → ℂˣ)
    (f : IndSp (points (Fin n)) ((ofChar (torusChar fun i => unrChar k (α i))).comp
      (leviTorus k (Fin n)).symm.toMonoidHom))
    (b : GL (Fin n) k) (hb : b ∈ borel k (Fin n)) (t : Fin n → kˣ)
    (ht : ∀ i, (b : Matrix (Fin n) (Fin n) k) i i = t i) (g : GL (Fin n) k) :
    f.1.1 (b * g) = (∏ i : Fin n, ((α i : ℂ) * (((resCard k : ℝ) ^ (((i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2) : ℝ) : ℂ))
      ^ ord k (t i)) * f.1.1 g := by
  refine (parInd_law _ _ f ⟨b, hb⟩ g).trans ?_
  show _ • ofChar _ _ (f.1.1 g) = _
  rw [ofChar_apply, torusChar_apply, deltaHalf_apply, smul_eq_mul, ← mul_assoc,
    Units.coe_prod, Units.coe_prod, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  have e : Matrix.GeneralLinearGroup.det (leviProj _ (points (Fin n)) ⟨b, hb⟩ i) = t i := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_unique]
    exact ht i
  show _ * ((unrChar k (α i)
    (Matrix.GeneralLinearGroup.det (leviProj _ (points (Fin n)) ⟨b, hb⟩ i)) : ℂˣ) : ℂ) = _
  have e2 : ((modExp (fun _ : Fin n => Unit) i : ℂ) / 2) =
      ((-(((i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2) : ℝ) : ℂ) := by
    rw [modExp_fin _ (fun _ => by simp)]
    push_cast
    ring
  have hq : (0 : ℝ) ≤ resCard k := Nat.cast_nonneg _
  rw [e, e2, val_absPow_ofReal, unrChar_apply, Units.val_zpow_eq_zpow_val, mul_zpow, mul_comm,
    GlobalTheory.LGrp.nabs_eq_zpow, ← Complex.ofReal_zpow, ← Real.rpow_intCast, ← Real.rpow_intCast,
    ← Real.rpow_mul hq, ← Real.rpow_mul hq]
  congr 3
  push_cast
  ring

theorem exists_sph : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (α : Fin n → ℂˣ), IsUnitarisable π → HasSatake π α → ∃ φ : GL (Fin n) k → ℂ, IsBorelSph k (fun i : Fin n => (α i : ℂ) * (((resCard k : ℝ) ^ (((i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2) : ℝ) : ℂ)) φ ∧ HasBoundedSums k φ := by
  intro k _ _ _ _ n V _ _ π α hu ⟨_, hs, S, f, hf⟩
  have hsm : IsSmooth S.toRepresentation :=
    IsSubquotient.isSmooth ⟨S, .id _, Function.surjective_id⟩ (isSmooth_parInd _ _)
  let E : S.toSubmodule →ₗ[ℂ] ℂ := ⟨⟨fun u => u.1.1.1 1, fun _ _ => rfl⟩, fun _ _ => rfl⟩
  have hr : ∀ u : S.toSubmodule, (∀ x ∈ KO k (Fin n), S.toRepresentation x u = u) →
      ∀ g, ∀ x ∈ KO k (Fin n), u.1.1.1 (g * x) = u.1.1.1 g := fun u h g x hx =>
    congrArg (fun z : S.toSubmodule => z.1.1.1 g) (h x hx)
  obtain ⟨w, hw, hw1, hb⟩ := exists_vector hsm hu SplitFlip.isCompact_KO f hf hs E fun u h h0 => by
    refine Subtype.ext (Subtype.ext (Subtype.ext (funext fun g => ?_)))
    obtain ⟨b, hb, x, hx, rfl⟩ := iwasawa_blockTriangular k (Fin n) Fin.val g
    have h1 := parInd_law _ _ u.1 ⟨b, (mem_borel _).2 hb⟩ 1
    have h2 : u.1.1.1 1 = 0 := h0
    rw [h2, map_zero, smul_zero, mul_one] at h1
    exact (hr u h b x hx).trans h1
  refine ⟨w.1.1.1, ⟨hr w hw, fun b hb t ht => ?_⟩, fun T hT => ?_⟩
  · have h1 := law α w.1 b hb t ht 1
    have h2 : w.1.1.1 1 = 1 := hw1
    rwa [h2, mul_one, mul_one] at h1
  · refine le_of_eq_of_le ?_ (hb T hT)
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    show _ = w.1.1.1 (1 * c.out)
    rw [one_mul]

end GlobalTheory.SatakeBound.Rep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasFiniteRankTraceOfOfRangeLeFiniteDimensional
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasFiniteRankTraceOfOfRangeLeFiniteDimensional
namespace GlobalTheory.IndefiniteRowSideFullHecke.RangeTrace

theorem hasFinTrace_of_range_le (X : Type) [AddCommGroup X] [Module ℂ X] (T : X →ₗ[ℂ] X)
    (Z : Submodule ℂ X) [FiniteDimensional ℂ Z] (hT : LinearMap.range T ≤ Z) :
    GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasFinTrace T (LinearMap.trace ℂ Z (T.restrict (p := Z) (q := Z)
      fun x _ => hT (LinearMap.mem_range_self T x))) := by
  haveI : FiniteDimensional ℂ (LinearMap.range T) := Submodule.finiteDimensional_of_le hT
  refine ⟨inferInstance, ?_⟩
  have hmem : ∀ x : Z, (T.restrict (p := Z) (q := Z)
      fun x _ => hT (LinearMap.mem_range_self T x)) x ∈ (LinearMap.range T).comap Z.subtype :=
    fun x => LinearMap.mem_range_self T (x : X)
  rw [← LinearMap.trace_restrict_eq_of_forall_mem _ _ hmem,
    ← LinearMap.trace_conj' _ (Submodule.comapSubtypeEquivOfLe hT)]
  congr 1

end GlobalTheory.IndefiniteRowSideFullHecke.RangeTrace
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasFiniteRankTraceOfOfRangeLeFiniteDimensionalStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasFiniteRankTraceOf_of_range_le_finiteDimensional : ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (T : X →ₗ[ℂ] X) (Z : Submodule ℂ X)
    [FiniteDimensional ℂ Z] (hT : LinearMap.range T ≤ Z),
    GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasFinTrace T (LinearMap.trace ℂ Z (T.restrict (p := Z) (q := Z)
      fun x _ => hT (LinearMap.mem_range_self T x))) := by
  first | exact @GlobalTheory.IndefiniteRowSideFullHecke.RangeTrace.hasFinTrace_of_range_le | exact GlobalTheory.IndefiniteRowSideFullHecke.RangeTrace.hasFinTrace_of_range_le | (intros; apply GlobalTheory.IndefiniteRowSideFullHecke.RangeTrace.hasFinTrace_of_range_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralIntegralGLMulRightComplexProductSigma
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Topology
open scoped ENNReal

namespace GlobalTheory.SmGL.IndDual

section Real

open GlobalTheory.SplitFlip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
  [MeasurableSpace k] [BorelSpace k]

theorem integral_KO_mul_right_real (μ : Measure (GL n k)) [μ.IsHaarMeasure] {f : GL n k → ℝ}
    (hf : Continuous f) (hlaw : ∀ (p : parab k e) x, f (p * x) = modulus k m (leviProj k e p) * f x)
    (g : GL n k) :
    ∫ x in (KO k n : Set (GL n k)), f (x * g) ∂μ = ∫ x in (KO k n : Set (GL n k)), f x ∂μ := by
  have h1 : IntegrableOn (fun x => f (x * g)) (KO k n : Set (GL n k)) μ :=
    (hf.comp (continuous_mul_const g)).continuousOn.integrableOn_compact isCompact_KO
  have h2 : IntegrableOn f (KO k n : Set (GL n k)) μ := hf.continuousOn.integrableOn_compact isCompact_KO
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part h1,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part h2,
    UnitInd.lintegral_KO_mul_right e μ (φ := fun x => ENNReal.ofReal (f x)) hf.measurable.ennreal_ofReal
      (fun p x => by rw [hlaw, ENNReal.ofReal_mul (modulus_pos k _).le]) g,
    UnitInd.lintegral_KO_mul_right e μ (φ := fun x => ENNReal.ofReal (-f x)) hf.neg.measurable.ennreal_ofReal
      (fun p x => by rw [hlaw, ← mul_neg, ENNReal.ofReal_mul (modulus_pos k _).le]) g]

theorem integral_integralGL_mul_right_complex_productSigma (μ : Measure (GL n k)) [μ.IsHaarMeasure] {F : GL n k → ℂ}
    (hF : Continuous F) (hlaw : ∀ (p : parab k e) x, F (p * x) = (modulus k m (leviProj k e p) : ℂ) * F x)
    (g : GL n k) :
    ∫ x in (KO k n : Set (GL n k)), F (x * g) ∂μ = ∫ x in (KO k n : Set (GL n k)), F x ∂μ := by
  have h1 : IntegrableOn (fun x => F (x * g)) (KO k n : Set (GL n k)) μ :=
    (hF.comp (continuous_mul_const g)).continuousOn.integrableOn_compact isCompact_KO
  have h2 : IntegrableOn F (KO k n : Set (GL n k)) μ := hF.continuousOn.integrableOn_compact isCompact_KO
  have hre := integral_KO_mul_right_real e μ (Complex.continuous_re.comp hF)
    (fun p x => by simp [hlaw]) g
  have him := integral_KO_mul_right_real e μ (Complex.continuous_im.comp hF)
    (fun p x => by simp [hlaw]) g
  refine Complex.ext ?_ ?_
  · exact ((integral_re h1).symm.trans hre).trans (integral_re h2)
  · exact ((integral_im h1).symm.trans him).trans (integral_im h2)

end Real

theorem integral_KO_mul_right : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) [MeasurableSpace (GL n k)] [BorelSpace (GL n k)] (μ : Measure (GL n k)) [μ.IsHaarMeasure] (F : GL n k → ℂ), Continuous F → (∀ (p : parab k e) (g : GL n k), F (p * g) = (modulus k m (leviProj k e p) : ℂ) * F g) → ∀ g : GL n k, ∫ x in (KO k n : Set (GL n k)), F (x * g) ∂μ = ∫ x in (KO k n : Set (GL n k)), F x ∂μ := by
  intro k _ _ _ _ α n m _ _ _ _ _ _ e M hM μ _ F hF hlaw g
  borelize k
  obtain rfl : M = Units.instMeasurableSpace :=
    hM.measurable_eq.trans (SplitFlip.borel_GL (k := k) (n := n)).measurable_eq.symm
  exact integral_integralGL_mul_right_complex_productSigma e μ hF hlaw g

end GlobalTheory.SmGL.IndDual
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEuclideanCoordsHermitianCartanInvolution
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEuclideanCoordsHermitianCartanInvolution
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace Real ComplexOrder

noncomputable section

namespace GlobalTheory.Twist.EuclidCoord

open GlobalTheory.RealWeil.UnitaryOsc

open scoped MatrixOrder in
theorem exists_coord : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (H s : Matrix ι ι ℂ), Hᴴ = H → s * s = 1 → (H * s).PosDef → ∃ (E : EuclideanSpace ℂ ι ≃L[ℝ] (ι → ℂ)) (J : EuclideanSpace ℂ ι ≃ₗᵢ[ℝ] EuclideanSpace ℂ ι), (∀ x, J (J x) = -x) ∧ (∀ x, E (J x) = I • s *ᵥ E x) ∧ ∀ x y, (star (E y) ⬝ᵥ H *ᵥ E x).im = omJ J x y := by
  intro ι _ _ H s hH hs hpos
  have hP0 : (0 : Matrix ι ι ℂ) ≤ H * s := hpos.posSemidef.nonneg
  set R : Matrix ι ι ℂ := CFC.sqrt (H * s)
  have hR0 : (0 : Matrix ι ι ℂ) ≤ R := CFC.sqrt_nonneg _
  have hRh : Rᴴ = R := hR0.posSemidef.isHermitian.eq
  have hRR : R * R = H * s := CFC.sqrt_mul_sqrt_self _ hP0
  have hdet : R.det ≠ 0 := by
    intro h0
    have e := congrArg Matrix.det hRR
    rw [det_mul, h0, zero_mul] at e
    exact (hpos.det_pos.ne') (by rw [← e])
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det R).2 hdet.isUnit
  set s₀ : Matrix ι ι ℂ := u.1 * s * (u⁻¹).1 with hs₀
  have hs₀2 : s₀ * s₀ = 1 := by
    simp only [hs₀, mul_assoc, Units.inv_mul_cancel_left]
    rw [← mul_assoc s, hs, one_mul, Units.mul_inv]

  have hRRs : u.1ᴴ * u.1 * s = H := by
    rw [hu, hRh, hRR, mul_assoc, hs, mul_one]
  have hform : (u⁻¹).1ᴴ * H * (u⁻¹).1 = s₀ := by
    rw [← hRRs]
    calc _ = (u.1 * (u⁻¹).1)ᴴ * (u.1 * s * (u⁻¹).1) := by simp only [mul_assoc, conjTranspose_mul]
      _ = s₀ := by simp [hs₀]
  have hs₀h : s₀ᴴ = s₀ := by
    rw [← hform, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hH, mul_assoc]
  let E : EuclideanSpace ℂ ι ≃L[ℝ] (ι → ℂ) :=
    (crd ι).trans (ContinuousLinearEquiv.equivOfInverse (mvL (u⁻¹).1) (mvL u.1)
      (fun v => by
        change u.1 *ᵥ (u⁻¹).1 *ᵥ v = v
        rw [mulVec_mulVec, Units.mul_inv, one_mulVec])
      (fun v => by
        change (u⁻¹).1 *ᵥ u.1 *ᵥ v = v
        rw [mulVec_mulVec, Units.inv_mul, one_mulVec]))
  have hE : ∀ x, E x = (u⁻¹).1 *ᵥ crd ι x := fun _ => rfl
  refine ⟨E, cplx s₀ hs₀h hs₀2, cplx_cplx s₀ hs₀h hs₀2, fun x => ?_, fun x y => ?_⟩
  · rw [hE, hE, crd_cplx, mulVec_smul, mulVec_mulVec, mulVec_mulVec]
    congr 2
    rw [hs₀, ← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul]
  · rw [omJ_cplx, hE, hE, form_mulVec, hform]

end GlobalTheory.Twist.EuclidCoord

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEuclideanCoordsHermitianCartanInvolutionStatement
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace Real ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_euclideanCoords_hermitian_cartanInvolution : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (H s : Matrix ι ι ℂ), Hᴴ = H → s * s = 1 → (H * s).PosDef → ∃ (E : EuclideanSpace ℂ ι ≃L[ℝ] (ι → ℂ)) (J : EuclideanSpace ℂ ι ≃ₗᵢ[ℝ] EuclideanSpace ℂ ι), (∀ x, J (J x) = -x) ∧ (∀ x, E (J x) = I • s *ᵥ E x) ∧ ∀ x y, (star (E y) ⬝ᵥ H *ᵥ E x).im = omJ J x y := by
  first | exact @GlobalTheory.Twist.EuclidCoord.exists_coord | exact GlobalTheory.Twist.EuclidCoord.exists_coord | (intros; apply GlobalTheory.Twist.EuclidCoord.exists_coord <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompactSubgroup
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)

namespace GlobalTheory.UnipCompact

variable {n : Type}

theorem conc_mul_sub (c : n → ℤ) (m : ℕ) : GlobalTheory.IwahoriInj.Conc fun i j => (m : ℤ) * (c i - c j) :=
  ⟨fun i => by simp, fun i j l => le_of_eq (by ring)⟩

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Fintype n] [DecidableEq n]

theorem isClosed_unipOf (c : n → ℤ) : IsClosed (GlobalTheory.InertSupp.unipOf k c : Set (GL n k)) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have e : (GlobalTheory.InertSupp.unipOf k c : Set (GL n k)) =
      ⋂ i, ⋂ j, ⋂ (_ : ¬ c i < c j), {g : GL n k | (g : Matrix n n k) i j = (1 : Matrix n n k) i j} := by
    ext g
    simp only [SetLike.mem_coe, mem_unipOf, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [e]
  refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => ?_
  exact isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const

theorem eventually_mem_grp {c : n → ℤ} {u : GL n k} (hu : u ∈ GlobalTheory.InertSupp.unipOf k c) :
    ∀ᶠ m : ℕ in Filter.atTop, u ∈ GlobalTheory.IwahoriInj.grp k (conc_mul_sub c m) := by
  have key : ∀ u ∈ GlobalTheory.InertSupp.unipOf k c, ∀ᶠ m : ℕ in Filter.atTop,
      ∀ i j, Deep ((m : ℤ) * (c i - c j)) (u.val i j) := by
    intro u hu
    simp only [Filter.eventually_all]
    intro i j
    by_cases h : c i < c j
    · filter_upwards [GlobalTheory.IwahoriInj.eventually_deep (u.val i j)] with m hm
      refine hm.mono ?_
      nlinarith [Int.natCast_nonneg m]
    · rw [GlobalTheory.InertSupp.mem_unipOf.1 hu i j h]
      refine Filter.Eventually.of_forall fun m => ?_
      by_cases hij : i = j
      · subst hij
        simp [GlobalTheory.IwahoriInj.deep_zero_iff]
      · simp [one_apply_ne hij, GlobalTheory.IwahoriInj.deep_zero]
  exact (key u hu).and (key _ (inv_mem hu))

theorem exists_compact_subgroup (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c : n → ℤ) (S : Finset (GL n k))
    (hS : ∀ u ∈ S, u ∈ GlobalTheory.InertSupp.unipOf k c) :
    ∃ H : Subgroup (GL n k), H ≤ GlobalTheory.InertSupp.unipOf k c ∧ IsCompact (H : Set (GL n k)) ∧ ∀ u ∈ S, u ∈ H := by
  obtain ⟨m, hm⟩ := ((Filter.eventually_all_finset S).2 fun u hu => eventually_mem_grp (hS u hu)).exists
  refine ⟨GlobalTheory.IwahoriInj.grp k (conc_mul_sub c m) ⊓ GlobalTheory.InertSupp.unipOf k c, inf_le_right, ?_,
    fun u hu => ⟨hm u hu, hS u hu⟩⟩
  rw [Subgroup.coe_inf]
  let f : n → n → ℤ := fun i j => (m : ℤ) * (c i - c j)
  have hK : IsCompact {A : Matrix n n k | ∀ i j, Deep (f i j) (A i j)} := by
    have h : IsCompact (Set.pi Set.univ fun i : n => Set.pi Set.univ fun j : n =>
        {x : k | Deep (f i j) x}) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
        IsNonarchimedeanLocalField.isCompact_closedBall k _
    have e : {A : Matrix n n k | ∀ i j, Deep (f i j) (A i j)} =
        (Set.pi Set.univ fun i : n => Set.pi Set.univ fun j : n =>
          {x : k | Deep (f i j) x}) :=
      Set.ext fun x => ⟨fun hx i _ j _ => hx i j, fun hx i j => hx i trivial j trivial⟩
    rw [e]
    exact h
  have h := (Units.isClosedEmbedding_embedProduct (α := Matrix n n k)).isCompact_preimage
    (hK.prod (hK.image MulOpposite.continuous_op))
  have hgrp : IsCompact (GlobalTheory.IwahoriInj.grp k (conc_mul_sub c m) : Set (GL n k)) := by
    convert h using 1
    ext g
    simp only [SetLike.mem_coe, Set.mem_ofPred_eq, Set.mem_preimage, Units.embedProduct_apply,
      Set.mem_prod, (MulOpposite.op_injective).mem_set_image]
    rfl
  exact hgrp.inter_right (isClosed_unipOf c)

end GlobalTheory.UnipCompact
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NabsDetEqOfActEq
section -- merged from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfPowerSpherical
open MeasureTheory ValuativeRel Matrix
open GlobalTheory.SplitWeil GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical

section Defs
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def chainGen (α α' : kˣ) (m j i : ℕ) : kˣ :=
  α ^ (-(j : ℤ)) * (α / α') ^ (m / 2) * (α * α') ^ (((m / 2 : ℕ) : ℤ) - (i : ℤ))

def frame (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (b : ℕ → kˣ) : GL (n ⊕ Fin c) k :=
  embA n ⟨Matrix.diagonal fun i : Fin c => (b (i.val + 1) : k),
    Matrix.diagonal fun i : Fin c => ((b (i.val + 1))⁻¹ : kˣ),
    by simp [Matrix.diagonal_mul_diagonal], by simp [Matrix.diagonal_mul_diagonal]⟩

variable [MeasurableSpace k] [BorelSpace k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

end Defs

section Statements
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

end Statements

section Chain
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

end Chain

section Basic₂
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical
end
end

open MeasureTheory ValuativeRel Matrix
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical GlobalTheory.LatPair GlobalTheory.StepData
open scoped Pointwise

noncomputable section
namespace GlobalTheory.IdealChain

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Act
variable {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

end Act

section Half

end Half

end GlobalTheory.IdealChain
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumProjectorRangeAnnihilated
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumProjectorRangeAnnihilated
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder

namespace GlobalTheory.Mem.Lift.VacAnn

private theorem hasFDerivAt_gau {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (w : V) :
    HasFDerivAt (_root_.GlobalTheory.RealWeil.gau : V → ℂ)
      ((-(Real.pi : ℂ) * _root_.GlobalTheory.RealWeil.gau w) • ((Complex.ofRealCLM).comp (innerSL ℝ w))) w := by
  have h1 : HasFDerivAt (fun u : V => ‖u‖ ^ 2) (2 • innerSL ℝ w) w := by
    simpa using (hasStrictFDerivAt_norm_sq w).hasFDerivAt
  have h2 := (Complex.ofRealCLM.hasFDerivAt).comp w h1
  have h3 := (h2.const_mul (-(Real.pi : ℂ) / 2)).cexp
  have hf : (_root_.GlobalTheory.RealWeil.gau : V → ℂ) =
      fun u => Complex.exp (-(Real.pi : ℂ) / 2 * ((‖u‖ ^ 2 : ℝ) : ℂ)) := by
    funext u; unfold _root_.GlobalTheory.RealWeil.gau; push_cast; ring_nf
  rw [hf]
  refine h3.congr_fderiv ?_
  ext y
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, Function.comp_apply,
    Complex.ofRealCLM_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul,
    ContinuousLinearMap.coe_smul', Pi.smul_apply]
  push_cast
  ring

theorem _root_.GlobalTheory.Mem.Lift.VacAnn.fderiv_gau_apply {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (w v : V) :
    fderiv ℝ (_root_.GlobalTheory.RealWeil.gau : V → ℂ) w v =
      -(Real.pi : ℂ) * ⟪w, v⟫ * _root_.GlobalTheory.RealWeil.gau w := by
  rw [(hasFDerivAt_gau w).fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, innerSL_apply_apply, smul_eq_mul]
  ring

theorem _root_.GlobalTheory.Mem.Lift.VacAnn.proj_annihilated : ∀ (V : Type) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (B : Type)
    [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (J : V ≃ₗᵢ[ℝ] V)
    (ρ : V → B →L[ℂ] B), (∀ x, J (J x) = -x) →
    ∀ (h : _root_.GlobalTheory.RealWeil.IsHeis (_root_.GlobalTheory.RealWeil.omJ J) ρ) (x : B) (z : V),
      _root_.GlobalTheory.Mem.Lift.dH ρ z (_root_.GlobalTheory.RealWeil.proj h x) +
        I • _root_.GlobalTheory.Mem.Lift.dH ρ (J z) (_root_.GlobalTheory.RealWeil.proj h x) = 0 := by
  intro V _ _ _ _ _ B _ _ _ J ρ hJ h x z
  set P := _root_.GlobalTheory.RealWeil.proj h
  set f := P x with hf_def
  have hf : _root_.GlobalTheory.RealWeil.Sm ρ f :=
    _root_.GlobalTheory.RealWeil.Good.sm hJ
      (_root_.GlobalTheory.RealWeil.Osc.good_proj hJ h x)
  have hsand : ∀ w : V, P (ρ w f) = _root_.GlobalTheory.RealWeil.gau w • f := fun w =>
    _root_.GlobalTheory.RealWeil.proj_heis_proj hJ h w x
  have hcomp : ∀ w v : V, P (ρ w (_root_.GlobalTheory.Mem.Lift.dH ρ v f)) =
      ((Real.pi : ℂ) * I * (⟪w, J v⟫ : ℝ) * _root_.GlobalTheory.RealWeil.gau w
        - (Real.pi : ℂ) * (⟪w, v⟫ : ℝ) * _root_.GlobalTheory.RealWeil.gau w) • f := by
    intro w v
    rw [_root_.GlobalTheory.Mem.Lift.VacBd.heis_dH h hf v w, map_add (f := _), map_smul, hsand w,
      _root_.GlobalTheory.Mem.Lift.VacBd.fderiv_compress P hf _root_.GlobalTheory.RealWeil.contDiff_gau hsand w v,
      _root_.GlobalTheory.Mem.Lift.VacAnn.fderiv_gau_apply, smul_smul, ← add_smul]
    congr 1
    show (Real.pi : ℂ) * I * ((⟪w, J v⟫ : ℝ) : ℂ) * _root_.GlobalTheory.RealWeil.gau w
        + -(Real.pi : ℂ) * ((⟪w, v⟫ : ℝ) : ℂ) * _root_.GlobalTheory.RealWeil.gau w = _
    ring
  set G := _root_.GlobalTheory.Mem.Lift.dH ρ z f + I • _root_.GlobalTheory.Mem.Lift.dH ρ (J z) f
  have hG : _root_.GlobalTheory.RealWeil.Sm ρ G :=
    _root_.GlobalTheory.RealWeil.Osc.sm_add (_root_.GlobalTheory.Mem.Lift.VacBd.sm_dH h hf z)
      (_root_.GlobalTheory.RealWeil.Osc.sm_smul I (_root_.GlobalTheory.Mem.Lift.VacBd.sm_dH h hf (J z)))
  have hzero : ∀ w : V, P (ρ w G) = 0 := by
    intro w
    simp only [G, map_add (f := _), map_smul, hcomp, smul_smul, ← add_smul, hJ z, inner_neg_right]
    apply smul_eq_zero_of_left
    push_cast
    ring_nf
    rw [I_sq]
    ring
  rw [← (_root_.GlobalTheory.RealWeil.Osc.good_of_sm hJ h hG).inversion hJ]
  have hzero' : ∀ w : V, _root_.GlobalTheory.RealWeil.proj h (ρ (-w) G) = 0 := fun w => hzero (-w)
  simp only [hzero', map_zero, integral_zero]

end GlobalTheory.Mem.Lift.VacAnn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumProjectorRangeAnnihilatedStatement
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace Real ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuumProjector_range_annihilated : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (J : V ≃ₗᵢ[ℝ] V) (ρ : V → B →L[ℂ] B), (∀ x, J (J x) = -x) → ∀ (h : IsHeis (omJ J) ρ) (x : B) (z : V), dH ρ z (proj h x) + I • dH ρ (J z) (proj h x) = 0 := by
  first | exact @GlobalTheory.Mem.Lift.VacAnn.proj_annihilated | exact GlobalTheory.Mem.Lift.VacAnn.proj_annihilated | (intros; apply GlobalTheory.Mem.Lift.VacAnn.proj_annihilated <;> assumption)
end
end
