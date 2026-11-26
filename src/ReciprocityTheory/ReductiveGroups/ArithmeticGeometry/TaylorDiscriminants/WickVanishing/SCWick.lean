module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantTheorems.WickFormula

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.SecondOrderIterateEqZero
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.LiftXHasSubst
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem liftX_hasSubst :
    HasSubst (fun p : Fin 1 × Fin d => (X (Sum.inl p.2) : AA k d)) := by
  first
  | exact hasSubst_of_constantCoeff_zero (fun p => by simp)
  | exact ⟨fun p => by simp, fun e => Set.toFinite _⟩

theorem liftX_add (f g : PS k 1 d) : liftX k (f + g) = liftX k f + liftX k g := MvPowerSeries.subst_add liftX_hasSubst f g

theorem liftX_mul (f g : PS k 1 d) : liftX k (f * g) = liftX k f * liftX k g := MvPowerSeries.subst_mul liftX_hasSubst f g

theorem Dof_add (F : Fin d → PS k 2 d) (u u' : Fin d → k) (f : PS k 1 d) :
    Dof F (u + u') f = Dof F u f + Dof F u' f := by
  unfold Dof
  simp only [Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem nabla_add (B : FB R d O) (h : PS k 2 d) (m : ℕ) (u u' φ φ' : Fin d → k) (G : AA k d) :
    nabla k B h m (u + u') (φ + φ') G = nabla k B h m u φ G + nabla k B h m u' φ' G := by
  first
  | (unfold nabla Dx
     simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add, map_add (f := _), add_mul, mul_add, Finset.sum_add_distrib, Dof_add,
       liftX_add, smul_add, add_smul]
     ring)
  | (unfold nabla
     revert G u u' φ φ' m h B
     done)

def nablaL (B : FB R d O) (h : PS k 2 d) (m : ℕ) (u φ : Fin d → k) : Module.End k (AA k d) where
  toFun := nabla k B h m u φ
  map_add' G G' := by
    simp only [nabla, Dx, Derivation.map_add, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' c G := by
    simp only [nabla, Dx, Derivation.map_smul, mul_smul_comm, RingHom.id_apply, smul_add,
      smul_sub, Finset.smul_sum]

@[simp] theorem nablaL_apply (B : FB R d O) (h : PS k 2 d) (m : ℕ) (u φ : Fin d → k) (G : AA k d) :
    nablaL B h m u φ G = nabla k B h m u φ G := rfl

theorem nablaL_add (B : FB R d O) (h : PS k 2 d) (m : ℕ) (u u' φ φ' : Fin d → k) :
    nablaL B h m (u + u') (φ + φ') = nablaL B h m u φ + nablaL B h m u' φ' := LinearMap.ext fun G => by
    simp only [LinearMap.add_apply, nablaL_apply]
    exact nabla_add B h m u u' φ φ' G

theorem nablaL_bracket (hN2 : ConnectionCommutator) (B : FB R d O) (h : PS k 2 d) (m : ℕ) (ξ η : (Fin d → k) × (Fin d → k)) :
    nablaL B h m ξ.1 ξ.2 * nablaL B h m η.1 η.2 - nablaL B h m η.1 η.2 * nablaL B h m ξ.1 ξ.2 =
      algebraMap k (Module.End k (AA k d)) ((m : k) * betaH k ξ η) := by
  unfold ConnectionCommutator at hN2
  apply LinearMap.ext
  intro G
  simp only [LinearMap.sub_apply, Module.End.mul_apply, nablaL_apply, Module.algebraMap_end_apply]
  first
  | exact hN2 B h m ξ η G
  | exact hN2 B h m ξ.1 ξ.2 η.1 η.2 G
  | exact hN2 B h m G ξ η
  | simpa using hN2 B h m ξ η G
  | simpa using hN2 B h m ξ.1 ξ.2 η.1 η.2 G
  | (apply hN2; done)
  | (simp only [Algebra.smul_def] at *; apply hN2; done)

theorem nablaL_comm (hN2 : ConnectionCommutator) (B : FB R d O) (h : PS k 2 d) (m : ℕ) (ξ η : (Fin d → k) × (Fin d → k))
    (hb : betaH k ξ η = 0) : Commute (nablaL B h m ξ.1 ξ.2) (nablaL B h m η.1 η.2) := by
  have hbr := nablaL_bracket hN2 B h m ξ η
  rw [hb, mul_zero, map_zero, sub_eq_zero] at hbr
  exact hbr

def sideE {ι : Type} [Fintype ι] (s : ι → Bool) :
    ι ≃ Fin (Fintype.card {l // s l = true}) ⊕ Fin (Fintype.card {l // ¬ s l = true}) :=
  (Equiv.sumCompl (fun l => s l = true)).symm.trans (Equiv.sumCongr (Fintype.equivFin _) (Fintype.equivFin _))

theorem sideE_symm_inl {ι : Type} [Fintype ι] (s : ι → Bool) (i : Fin (Fintype.card {l // s l = true})) :
    (sideE s).symm (Sum.inl i) = ((Fintype.equivFin {l // s l = true}).symm i).1 := rfl

theorem sideE_symm_inr {ι : Type} [Fintype ι] (s : ι → Bool) (j : Fin (Fintype.card {l // ¬ s l = true})) :
    (sideE s).symm (Sum.inr j) = ((Fintype.equivFin {l // ¬ s l = true}).symm j).1 := rfl

theorem side_inl {ι : Type} [Fintype ι] (s : ι → Bool) (i : Fin (Fintype.card {l // s l = true})) :
    s ((sideE s).symm (Sum.inl i)) = true := by
  rw [sideE_symm_inl]
  exact ((Fintype.equivFin {l // s l = true}).symm i).2

theorem side_inr {ι : Type} [Fintype ι] (s : ι → Bool) (j : Fin (Fintype.card {l // ¬ s l = true})) :
    s ((sideE s).symm (Sum.inr j)) = false := by
  rw [sideE_symm_inr]
  simpa using ((Fintype.equivFin {l // ¬ s l = true}).symm j).2

section Bridge

variable {ι : Type} [Fintype ι]

theorem foldr_eq_prod (f : ι → AA k d → AA k d) (F : ι → Module.End k (AA k d)) (hF : ∀ l, ⇑(F l) = f l)
    (n : ι →₀ ℕ) (L : List ι) (G : AA k d) :
    L.foldr (fun l g => (f l)^[n l] g) G = (L.map fun l => F l ^ n l).prod G := by
  induction L with
  | nil => simp
  | cons a L ih =>
    first
    | simp only [List.foldr_cons, List.map_cons, List.prod_cons, Module.End.mul_apply, Module.End.pow_apply, hF, ih]
    | simp only [List.foldr_cons, List.map_cons, List.prod_cons, LinearMap.mul_apply, LinearMap.pow_apply, hF, ih]

theorem perm_inl (s : ι → Bool) :
    ((Finset.univ : Finset ι).toList.filter (fun l => s l)).Perm
      (List.ofFn fun i => (sideE s).symm (Sum.inl i)) := by
  rw [List.perm_ext_iff_of_nodup ((Finset.nodup_toList _).filter _) ?_]
  · intro x
    simp only [List.mem_filter, Finset.mem_toList, Finset.mem_univ, true_and, List.mem_ofFn, Set.mem_range]
    constructor
    · intro hx
      exact ⟨Fintype.equivFin _ ⟨x, hx⟩, by rw [sideE_symm_inl]; simp⟩
    · rintro ⟨i, rfl⟩
      exact side_inl s i
  · rw [List.nodup_ofFn]
    intro i j hij
    simpa using congrArg (sideE s) hij

theorem perm_inr (s : ι → Bool) :
    ((Finset.univ : Finset ι).toList.filter (fun l => !s l)).Perm
      (List.ofFn fun j => (sideE s).symm (Sum.inr j)) := by
  rw [List.perm_ext_iff_of_nodup ((Finset.nodup_toList _).filter _) ?_]
  · intro x
    simp only [List.mem_filter, Finset.mem_toList, Finset.mem_univ, true_and, List.mem_ofFn, Set.mem_range,
      Bool.not_eq_true']
    constructor
    · intro hx
      exact ⟨Fintype.equivFin _ ⟨x, by simp [hx]⟩, by rw [sideE_symm_inr]; simp⟩
    · rintro ⟨j, rfl⟩
      exact side_inr s j
  · rw [List.nodup_ofFn]
    intro i j hij
    simpa using congrArg (sideE s) hij

theorem prod_perm_comm {A : Type} [Monoid A] {L L' : List A} (hp : L.Perm L')
    (hc : ∀ x ∈ L, ∀ y ∈ L, Commute x y) : L.prod = L'.prod := hp.prod_eq' (List.pairwise_of_forall_mem_list hc)

abbrev opL (B : FB R d O) (h : PS k 2 d) (m : ℕ) (s : ι → Bool) (ξ : ι → (Fin d → k) × (Fin d → k))
    (i : Fin (Fintype.card {l // s l = true})) : Module.End k (AA k d) :=
  nablaL B h m (ξ ((sideE s).symm (Sum.inl i))).1 (ξ ((sideE s).symm (Sum.inl i))).2

abbrev opR (B : FB R d O) (h : PS k 2 d) (m : ℕ) (s : ι → Bool) (ξ : ι → (Fin d → k) × (Fin d → k))
    (j : Fin (Fintype.card {l // ¬ s l = true})) : Module.End k (AA k d) :=
  nablaL B h m (ξ ((sideE s).symm (Sum.inr j))).1 (ξ ((sideE s).symm (Sum.inr j))).2

theorem ordNabla_eq (B : FB R d O) (h : PS k 2 d) (m : ℕ) (s : ι → Bool) (ξ : ι → (Fin d → k) × (Fin d → k))
    (hc : ∀ l l', s l = s l' → Commute (nablaL B h m (ξ l).1 (ξ l).2) (nablaL B h m (ξ l').1 (ξ l').2))
    (P : MvPolynomial ι k) (G : AA k d) :
    ordNabla k B h m s ξ P G =
      PI.WickFormula.ordEval (opL B h m s ξ) (opR B h m s ξ) (MvPolynomial.rename (sideE s) P) G := by
  classical
  set F : ι → Module.End k (AA k d) := fun l => nablaL B h m (ξ l).1 (ξ l).2 with hFdef
  unfold ordNabla PI.WickFormula.ordEval
  rw [LinearMap.sum_apply, MvPolynomial.support_rename_of_injective (sideE s).injective,
    Finset.sum_image (fun x _ y _ hxy => Finsupp.mapDomain_injective (sideE s).injective hxy)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [MvPolynomial.coeff_rename_mapDomain _ (sideE s).injective, LinearMap.smul_apply, smul_eq_C_mul,
    Module.End.mul_apply]
  congr 1
  rw [foldr_eq_prod (fun l => nabla k B h m (ξ l).1 (ξ l).2) F (fun _ => rfl) n,
    foldr_eq_prod (fun l => nabla k B h m (ξ l).1 (ξ l).2) F (fun _ => rfl) n]
  simp only [Finsupp.mapDomain_equiv_apply]
  have hS : (((Finset.univ : Finset ι).toList.filter (fun l => s l)).map fun l => F l ^ n l).prod =
      (List.ofFn fun i => opL B h m s ξ i ^ n ((sideE s).symm (Sum.inl i))).prod := by
    rw [show (fun i => opL B h m s ξ i ^ n ((sideE s).symm (Sum.inl i))) =
      (fun l => F l ^ n l) ∘ (fun i => (sideE s).symm (Sum.inl i)) from rfl, ← List.map_ofFn]
    refine prod_perm_comm ((perm_inl s).map _) ?_
    intro x hx y hy
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
    obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hy
    have e : s l = s l' := by
      rw [(List.mem_filter.mp hl).2, (List.mem_filter.mp hl').2]
    exact (hc l l' e).pow_pow _ _
  have hC : (((Finset.univ : Finset ι).toList.filter (fun l => !s l)).map fun l => F l ^ n l).prod =
      (List.ofFn fun j => opR B h m s ξ j ^ n ((sideE s).symm (Sum.inr j))).prod := by
    rw [show (fun j => opR B h m s ξ j ^ n ((sideE s).symm (Sum.inr j))) =
      (fun l => F l ^ n l) ∘ (fun j => (sideE s).symm (Sum.inr j)) from rfl, ← List.map_ofFn]
    refine prod_perm_comm ((perm_inr s).map _) ?_
    intro x hx y hy
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
    obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hy
    have e : s l = s l' := by
      have a := (List.mem_filter.mp hl).2
      have b := (List.mem_filter.mp hl').2
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at a b
      rw [a, b]
    exact (hc l l' e).pow_pow _ _
  rw [hS, hC]

end Bridge

end ReciprocityTheory.ChartRestriction.G.TB.SCPf
end
end

set_option autoImplicit false

noncomputable section

open MvPolynomial

namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf

variable {k : Type} [CommRing k] {ι : Type} [Fintype ι]

theorem sum_side {M : Type} [AddCommMonoid M] (s : ι → Bool) (g : ι → ι → M)
    (hg : ∀ l l', g l l' ≠ 0 → s l = true ∧ s l' = false) :
    ∑ l, ∑ l', g l l' = ∑ i, ∑ j, g ((sideE s).symm (Sum.inl i)) ((sideE s).symm (Sum.inr j)) := by
  have h1 : ∀ l, ∑ l', g l l' = ∑ j, g l ((sideE s).symm (Sum.inr j)) := by
    intro l
    rw [← Equiv.sum_comp (sideE s).symm (g l), Fintype.sum_sum_type]
    have h0 : ∑ i, g l ((sideE s).symm (Sum.inl i)) = 0 := by
      refine Finset.sum_eq_zero (fun i _ => ?_)
      by_contra hne
      have h2 := (hg _ _ hne).2
      rw [side_inl s i] at h2
      simp at h2
    rw [h0, zero_add]
  rw [Finset.sum_congr rfl (fun l _ => h1 l),
    ← Equiv.sum_comp (sideE s).symm (fun l => ∑ j, g l ((sideE s).symm (Sum.inr j))),
    Fintype.sum_sum_type]
  have h3 : ∑ j, ∑ j', g ((sideE s).symm (Sum.inr j)) ((sideE s).symm (Sum.inr j')) = 0 := by
    refine Finset.sum_eq_zero (fun j _ => Finset.sum_eq_zero (fun j' _ => ?_))
    by_contra hne
    have h2 := (hg _ _ hne).1
    rw [side_inr s j] at h2
    simp at h2
  rw [h3, add_zero]

abbrev kapE (s : ι → Bool) (κ : ι → ι → k) (i : Fin (Fintype.card {l // s l = true}))
    (j : Fin (Fintype.card {l // ¬ s l = true})) : k :=
  κ ((sideE s).symm (Sum.inl i)) ((sideE s).symm (Sum.inr j))

theorem delta_rename (s : ι → Bool) (κ : ι → ι → k) (hκ : ∀ l l', κ l l' ≠ 0 → s l = true ∧ s l' = false)
    (P : MvPolynomial ι k) :
    PI.WickFormula.delta (kapE s κ) (rename (sideE s) P) = rename (sideE s) (secondOrder k κ P) := by
  have hd : ∀ (x : Fin (Fintype.card {l // s l = true}) ⊕ Fin (Fintype.card {l // ¬ s l = true}))
      (Q : MvPolynomial ι k),
      pderiv x (rename (sideE s) Q) = rename (sideE s) (pderiv ((sideE s).symm x) Q) := by
    intro x Q
    conv_lhs => rw [← (sideE s).apply_symm_apply x]
    exact pderiv_rename (sideE s).injective _ _
  rw [PI.WickFormula.delta_eq_gdelta, PI.WickFormula.Gen.gdelta_apply,
    show secondOrder k κ P = ∑ l, ∑ l', C (κ l l') * pderiv l (pderiv l' P) from rfl]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, rename_C]
  rw [sum_side s _ ?_]
  · refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [smul_eq_C_mul, hd, hd]
  · intro l l' hne
    apply hκ
    intro h0
    apply hne
    rw [h0, map_zero, zero_mul]

theorem delta_pow_rename (s : ι → Bool) (κ : ι → ι → k)
    (hκ : ∀ l l', κ l l' ≠ 0 → s l = true ∧ s l' = false) (n : ℕ) (P : MvPolynomial ι k) :
    (PI.WickFormula.delta (kapE s κ) ^ n) (rename (sideE s) P) =
      rename (sideE s) ((secondOrder k κ)^[n] P) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, delta_rename s κ hκ, Function.iterate_succ_apply']

section Van

variable {π : Type} [Fintype π] [DecidableEq π]

theorem pairMin_step (c : ι → π) (s : ι → Bool) (n : ι →₀ ℕ) (l l' : ι) (hc : c l = c l')
    (hs : s l = true) (hs' : s l' = false) :
    pairMin c s (n + Finsupp.single l 1 + Finsupp.single l' 1) = pairMin c s n + 1 := by
  have key : ∀ q : π,
      min (∑ x ∈ Finset.univ.filter (fun x => c x = q ∧ s x = true),
          (n + Finsupp.single l 1 + Finsupp.single l' 1 : ι →₀ ℕ) x)
        (∑ x ∈ Finset.univ.filter (fun x => c x = q ∧ s x = false),
          (n + Finsupp.single l 1 + Finsupp.single l' 1 : ι →₀ ℕ) x) =
      min (∑ x ∈ Finset.univ.filter (fun x => c x = q ∧ s x = true), n x)
        (∑ x ∈ Finset.univ.filter (fun x => c x = q ∧ s x = false), n x) +
        if c l = q then 1 else 0 := by
    intro q
    classical
    simp only [Finsupp.add_apply, Finset.sum_add_distrib, Finsupp.single_apply, Finset.sum_ite_eq,
      Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hq : c l = q
    · have hq' : c l' = q := hc ▸ hq
      simp [hq, hq', hs, hs']
      try omega
    · have hq' : ¬ c l' = q := hc ▸ hq
      simp only [hq, hq', false_and, if_false]
      omega
  simp only [pairMin]
  rw [Finset.sum_congr rfl (fun q _ => key q), Finset.sum_add_distrib, Finset.sum_ite_eq]
  simp

theorem secondOrder_support (c : ι → π) (s : ι → Bool) (κ : ι → ι → k)
    (hκ : ∀ l l', κ l l' ≠ 0 → c l = c l' ∧ s l = true ∧ s l' = false) (Q : MvPolynomial ι k) (p j : ℕ)
    (hQ : ∀ n ∈ Q.support, pairMin c s n + j ≤ p) :
    ∀ n ∈ (secondOrder k κ Q).support, pairMin c s n + (j + 1) ≤ p := by
  intro n hn
  rw [MvPolynomial.mem_support_iff] at hn
  have h1 : AddMonoidAlgebra.coeff (secondOrder k κ Q) n = ∑ l, ∑ l', κ l l' * AddMonoidAlgebra.coeff (pderiv l (pderiv l' Q)) n := by
    rw [show secondOrder k κ Q = ∑ l, ∑ l', C (κ l l') * pderiv l (pderiv l' Q) from rfl]
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]
  rw [h1] at hn
  obtain ⟨l, -, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  obtain ⟨l', -, hl'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hl
  have hκ0 : κ l l' ≠ 0 := left_ne_zero_of_mul hl'
  have hc0 : AddMonoidAlgebra.coeff (pderiv l (pderiv l' Q)) n ≠ 0 := right_ne_zero_of_mul hl'
  rw [MvPolynomial.coeff_pderiv, MvPolynomial.coeff_pderiv] at hc0
  have hQn : n + Finsupp.single l 1 + Finsupp.single l' 1 ∈ Q.support := by
    rw [MvPolynomial.mem_support_iff]
    intro h0
    apply hc0
    rw [h0, zero_mul, zero_mul]
  obtain ⟨hcl, hsl, hsl'⟩ := hκ l l' hκ0
  have h2 := hQ _ hQn
  rw [pairMin_step c s n l l' hcl hsl hsl'] at h2
  omega

theorem secondOrder_iterate_eq_zero (c : ι → π) (s : ι → Bool) (κ : ι → ι → k)
    (hκ : ∀ l l', κ l l' ≠ 0 → c l = c l' ∧ s l = true ∧ s l' = false) (P : MvPolynomial ι k) (e : ℕ)
    (hP : ∀ n ∈ P.support, pairMin c s n ≤ e) (j : ℕ) (hj : e < j) :
    (secondOrder k κ)^[j] P = 0 := by
  have h : ∀ t, ∀ n ∈ ((secondOrder k κ)^[t] P).support, pairMin c s n + t ≤ e := by
    intro t
    induction t with
    | zero => simpa using hP
    | succ t ih =>
      rw [Function.iterate_succ_apply']
      exact secondOrder_support c s κ hκ _ e t ih
  by_contra hne
  obtain ⟨n, hn⟩ : ((secondOrder k κ)^[j] P).support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
    exact hne
  have h2 := h j n hn
  omega

end Van

end ReciprocityTheory.ChartRestriction.G.TB.SCPf
end
end

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem betaH_zero_zero (φ φ' : Fin d → k) : betaH k (0, φ) (0, φ') = 0 := by
  simp [betaH]

theorem betaH_antisymm (ξ η : (Fin d → k) × (Fin d → k)) : betaH k ξ η = -betaH k η ξ := by
  unfold betaH
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

def kapW (m : ℕ) {ι : Type} (s : ι → Bool) (ξa ξb : ι → (Fin d → k) × (Fin d → k)) (l l' : ι) : k :=
  if s l = true ∧ s l' = false then (m : k) * betaH k (ξb l) (ξa l') else 0

theorem kapW_supp (m : ℕ) {ι : Type} (s : ι → Bool) (ξa ξb : ι → (Fin d → k) × (Fin d → k)) (l l' : ι)
    (h : kapW m s ξa ξb l l' ≠ 0) : s l = true ∧ s l' = false := by
  unfold kapW at h
  by_contra hc
  exact h (if_neg hc)

theorem ordNabla_wick (hN2 : ConnectionCommutator) (hN3 : ConnectionKillsSeries) (B : FB R d O) (h : PS k 2 d) (m : ℕ) {ι : Type}
    [Fintype ι] (s : ι → Bool) (ξa ξb : ι → (Fin d → k) × (Fin d → k)) (hb0 : ∀ l, (ξb l).1 = 0)
    (haa : ∀ l l', s l = s l' → betaH k (ξa l) (ξa l') = 0)
    (hab : ∀ l l', s l = s l' → betaH k (ξa l) (ξb l') = 0) (P : MvPolynomial ι k) (f : PS k 1 d) :
    ordNabla k B h m s (fun l => ξa l + ξb l) P (liftX k f) =
      ∑ n ∈ Finset.range ((MvPolynomial.rename (sideE s) P).totalDegree + 1),
        PI.WickFormula.ordEval (opL B h m s ξa) (opR B h m s ξa)
          (((n.factorial : ℚ)⁻¹) • MvPolynomial.rename (sideE s) ((secondOrder k (kapW m s ξa ξb))^[n] P))
          (liftX k f) := by
  have hbb : ∀ l l', betaH k (ξb l) (ξb l') = 0 := fun l l' => by
    rw [show ξb l = (0, (ξb l).2) from Prod.ext (hb0 l) rfl, show ξb l' = (0, (ξb l').2) from Prod.ext (hb0 l') rfl]
    exact betaH_zero_zero _ _
  have hba : ∀ l l', s l = s l' → betaH k (ξb l) (ξa l') = 0 := fun l l' e => by
    rw [betaH_antisymm, hab l' l e.symm, neg_zero]
  have cA : ∀ l l', s l = s l' → Commute (nablaL B h m (ξa l).1 (ξa l).2) (nablaL B h m (ξa l').1 (ξa l').2) :=
    fun l l' e => nablaL_comm hN2 B h m _ _ (haa l l' e)
  have cAB : ∀ l l', s l = s l' → Commute (nablaL B h m (ξa l).1 (ξa l).2) (nablaL B h m (ξb l').1 (ξb l').2) :=
    fun l l' e => nablaL_comm hN2 B h m _ _ (hab l l' e)
  have cBA : ∀ l l', s l = s l' → Commute (nablaL B h m (ξb l).1 (ξb l).2) (nablaL B h m (ξa l').1 (ξa l').2) :=
    fun l l' e => nablaL_comm hN2 B h m _ _ (hba l l' e)
  have cB : ∀ l l', Commute (nablaL B h m (ξb l).1 (ξb l).2) (nablaL B h m (ξb l').1 (ξb l').2) :=
    fun l l' => nablaL_comm hN2 B h m _ _ (hbb l l')
  have hsum : ∀ l, nablaL B h m (ξa l + ξb l).1 (ξa l + ξb l).2 =
      nablaL B h m (ξa l).1 (ξa l).2 + nablaL B h m (ξb l).1 (ξb l).2 := fun l =>
    nablaL_add B h m _ _ _ _
  have cAll : ∀ l l', s l = s l' → Commute (nablaL B h m (ξa l + ξb l).1 (ξa l + ξb l).2)
      (nablaL B h m (ξa l' + ξb l').1 (ξa l' + ξb l').2) := fun l l' e => by
    rw [hsum, hsum]
    exact ((cA l l' e).add_right (cAB l l' e)).add_left ((cBA l l' e).add_right (cB l l'))
  rw [ordNabla_eq B h m s (fun l => ξa l + ξb l) cAll P (liftX k f)]
  have hL : opL B h m s (fun l => ξa l + ξb l) = opL B h m s ξa + opL B h m s ξb := funext fun i => hsum _
  have hR : opR B h m s (fun l => ξa l + ξb l) = opR B h m s ξa + opR B h m s ξb := funext fun j => hsum _
  have key := _root_.wick_formula k (Module.End k (AA k d)) (AA k d) _ _ (opL B h m s ξa) (opL B h m s ξb)
    (opR B h m s ξa) (opR B h m s ξb) (kapE s (kapW m s ξa ξb)) (liftX k f)
    (fun i i' => ⟨cA _ _ (by rw [side_inl s i, side_inl s i']), cAB _ _ (by rw [side_inl s i, side_inl s i']),
      cB _ _⟩)
    (fun j j' => ⟨cA _ _ (by rw [side_inr s j, side_inr s j']), cAB _ _ (by rw [side_inr s j, side_inr s j']),
      cB _ _⟩)
    (fun i j => cB _ _)
    (fun i j => by
      rw [nablaL_bracket hN2 B h m]
      unfold kapE kapW
      rw [if_pos ⟨side_inl s i, side_inr s j⟩])
    (fun i => by
      rw [Module.End.smul_def, opL, hb0]
      exact hN3 R d O k B h m _ f)
    (fun j => by
      rw [Module.End.smul_def, opR, hb0]
      exact hN3 R d O k B h m _ f)
    (MvPolynomial.rename (sideE s) P)
  rw [hL, hR, ← Module.End.smul_def, key]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Module.End.smul_def, delta_pow_rename s _ (kapW_supp m s ξa ξb)]

theorem ordNabla_u (hN2 : ConnectionCommutator) (B : FB R d O) (h : PS k 2 d) (m : ℕ) {ι : Type} [Fintype ι] (s : ι → Bool)
    (u : ι → Fin d → k) (P : MvPolynomial ι k) (G : AA k d) :
    ordNabla k B h m s (fun l => (u l, 0)) P G = nablaPoly k B h m u P G := by
  have hcomm : ∀ a b : ι, Function.Commute (nabla k B h m (u a) 0) (nabla k B h m (u b) 0) := by
    intro a b z
    have hz := hN2 R d O k B h m (u a, 0) (u b, 0) z
    have hb : betaH k (u a, (0 : Fin d → k)) (u b, 0) = 0 := by simp [betaH]
    rw [hb, mul_zero, map_zero, zero_mul] at hz
    exact sub_eq_zero.mp hz
  unfold ordNabla nablaPoly
  refine Finset.sum_congr rfl fun n _ => ?_
  congr 1
  rw [← List.foldr_append]
  refine List.Perm.foldr_eq' (List.filter_append_perm _ _) ?_ _
  intro x _ y _ z
  exact (hcomm y x).iterate_iterate (n y) (n x) z

end ReciprocityTheory.ChartRestriction.G.TB.SCPf
