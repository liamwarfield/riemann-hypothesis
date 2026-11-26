module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.EvCob
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.Imports
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.SpanForSubsingleton

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.SAffOfParts
noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.SplitAffineSpectral

open GluingInclusion

private theorem monoidHom_partialProd_comm {P : Type} [Group P] (σ : P →* P) {k : ℕ} (g : Fin k → P) (i : Fin (k + 1)) :
    σ (Fin.partialProd g i) = Fin.partialProd (fun l => σ (g l)) i := by
  induction i using Fin.induction with
  | zero => simp [Fin.partialProd_zero]
  | succ i ih => rw [Fin.partialProd_succ, Fin.partialProd_succ, map_mul, ih]

private theorem H_affine_combination_eq_of_quadratic_relation (hCh : SChain) (hSep : SSep) (hCore : Core) (hEv : EvCob)
    {P Q : Type} [Group P] [Group Q] (pr : P →* Q) (s : Q →* P) (hs : ∀ g, pr (s g) = g)
    (u : Q) (hu : ∀ g, g * u = u * g) {m : ℕ} (hC : ColPoly pr s u m) {j : ℕ} (hj : j + 1 ≤ m)
    (w : Chn P (j + 1)) (hw : IsCyc w) : IsBd (w - cmap (s.comp pr) (j + 1) w) := by
  set σ := s.comp pr with hσdef
  have hσσ : ∀ x, σ (σ x) = σ x := by intro x; simp [σ, hs]
  have hcyc : IsCyc (w - cmap σ (j + 1) w) := by
    unfold IsCyc at hw ⊢
    rw [map_sub, hCh.2.1 P P σ j w, hw, map_zero, sub_zero]
  by_contra hnb
  obtain ⟨c, hcI, hcd, hce⟩ := hSep P j _ hcyc hnb
  set c' : (Fin (j + 2) → P) → ℝ := fun y => c y - c (fun i => σ (y i)) with hc'
  have hI : InvS Set.univ c' := by
    intro g _ y
    have h1 := hcI g y
    have h2 := hcI (σ g) (fun i => σ (y i))
    simp only [MonoidHom.id_apply, smul_eq_mul] at h1 h2
    simp only [c', map_mul, h1, h2]
  have hd : dc c' = 0 := by
    funext y
    have e1 := congrFun hcd y
    have e2 := congrFun hcd (fun i => σ (y i))
    simp only [dC, Pi.zero_apply] at e1 e2
    simp only [dc, c', Pi.zero_apply, mul_sub, Finset.sum_sub_distrib, e1, e2, sub_zero]
  have hvan : ∀ y : Fin (j + 2) → Q, c' (fun i => s (y i)) = 0 := by
    intro y; simp [c', σ, hs]
  obtain ⟨e, heI, hce'⟩ := hCore P Q pr s hs u hu m hC j hj c' hI hd hvan
  have heI' : Inv (MonoidHom.id P) e := by
    intro g y
    simpa using heI g (Set.mem_univ g) y
  have hev0 := hEv P j e heI' _ hcyc
  apply hce
  have hdd : dC e = c' := hce'.symm
  rw [hdd] at hev0
  rw [← hev0]
  unfold ev
  simp only [c', mul_sub, Finsupp.sum_sub]
  rw [eq_comm, sub_eq_self]
  have hcm : cmap σ (j + 1) w = Finsupp.mapDomain (fun g i => σ (g i)) w := rfl
  rw [hcm, Finsupp.sum_sub_index (by intros; ring),
    Finsupp.sum_mapDomain_index (by intros; simp) (by intros; ring)]
  simp only [MonoidHom.id_apply, smul_eq_mul, mul_one, monoidHom_partialProd_comm, hσσ, sub_self]

private theorem aeval_mapOp_dc_comm {A : Type} (φ : A → A) (k : ℕ) (f : Polynomial ℝ)
    (e : (Fin (k + 1) → A) → ℝ) :
    Polynomial.aeval (mapOp φ (k + 2)) f (dc e) = dc (Polynomial.aeval (mapOp φ (k + 1)) f e) := by
  have hadd : ∀ a b : (Fin (k + 1) → A) → ℝ, dc (a + b) = dc a + dc b := by
    intro a b; funext y; simp [dc, mul_add, Finset.sum_add_distrib]
  have hsmul : ∀ (t : ℝ) (a : (Fin (k + 1) → A) → ℝ), dc (t • a) = t • dc a := by
    intro t a; funext y; simp [dc, Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
  have hpow : ∀ (N : ℕ) (a : (Fin (k + 1) → A) → ℝ),
      (mapOp φ (k + 2) ^ N) (dc a) = dc ((mapOp φ (k + 1) ^ N) a) := by
    intro N
    induction N with
    | zero => intro a; rfl
    | succ N ih =>
      intro a
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply]
      have : mapOp φ (k + 2) (dc a) = dc (mapOp φ (k + 1) a) := rfl
      rw [this, ih]
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), LinearMap.add_apply, hp, hq, hadd]
  | monomial N a =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, hpow, hsmul]

private theorem invS_aeval_mapOp_of_invS_of_mul_hom {A : Type} [Group A] (φ : A → A) (hφ : ∀ x y, φ (x * y) = φ x * φ y)
    (k : ℕ) (f : Polynomial ℝ) (e : (Fin k → A) → ℝ) (he : InvS Set.univ e) :
    InvS Set.univ (Polynomial.aeval (mapOp φ k) f e) := by
  have hpow : ∀ (N : ℕ) (a : (Fin k → A) → ℝ), InvS Set.univ a →
      InvS Set.univ ((mapOp φ k ^ N) a) := by
    intro N
    induction N with
    | zero => intro a ha; simpa using ha
    | succ N ih =>
      intro a ha
      rw [pow_succ, Module.End.mul_apply]
      apply ih
      intro g _ y
      show a (fun i => φ (g * y i)) = a (fun i => φ (y i))
      simp only [hφ]
      exact ha (φ g) (Set.mem_univ _) _
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    intro g hg y
    simp only [map_add (f := _), LinearMap.add_apply, Pi.add_apply, hp g hg y, hq g hg y]
  | monomial N a =>
    intro g hg y
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      Pi.smul_apply, smul_eq_mul]
    rw [hpow N e he g hg y]

private theorem aPoly_mulV_of_unit_place_monomials_ne_one (hSpan : Span) (hEig : Eigen) {L : Type} [Field L] [NumberField L]
    (hL : IsTotallyComplex L) (m : ℕ) (v : (𝓞 L)ˣ)
    (hv : ∀ a : InfinitePlace L → ℕ, 0 < ∑ w, a w → ∑ w, a w ≤ m →
      ∏ w, w (algebraMap (𝓞 L) L ↑v) ^ a w ≠ 1) (n r : ℕ) :
    APoly (Multiplicative (Matrix (Fin n) (Fin r) (𝓞 L))) (mulV n r ↑v) m := by
  intro q hq
  obtain ⟨f, hf1, hf⟩ := hEig L hL m v hv n r q hq
  refine ⟨f, hf1, ?_⟩
  intro c hcI hcd
  haveI : Module.Free ℤ (Additive (Multiplicative (Matrix (Fin n) (Fin r) (𝓞 L)))) :=
    (inferInstance : Module.Free ℤ (Matrix (Fin n) (Fin r) (𝓞 L)))
  haveI : Module.Finite ℤ (Additive (Multiplicative (Matrix (Fin n) (Fin r) (𝓞 L)))) :=
    (inferInstance : Module.Finite ℤ (Matrix (Fin n) (Fin r) (𝓞 L)))
  obtain ⟨k, a, α, e, heI, rfl⟩ := hSpan _ q c hcI hcd
  refine ⟨Polynomial.aeval (mapOp (mulV n r ↑v) (q + 1)) f e, ?_, ?_⟩
  · apply invS_aeval_mapOp_of_invS_of_mul_hom _ _ _ _ _ heI
    intro x y
    unfold mulV
    simp [smul_add]
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_add (f := _), map_sum]
      simp only [map_smul, hf, smul_zero, Finset.sum_const_zero, zero_add]
      exact aeval_mapOp_dc_comm _ q f e

theorem sAff_of_parts (hCh : SChain) (hSep : SSep) (hCore : Core) (hTr : Transfer) (hSpan : Span)
    (hUnit : Unit) (hEig : Eigen) (hEv : EvCob) : SAff := by
  intro L _ _ hL k hk n r H _ f f₀ hblock z hz
  obtain ⟨v, hv⟩ := hUnit L hL (k + 1) hk
  let ψ : GL (Fin n) (𝓞 L) →* MulAut (Multiplicative (Matrix (Fin n) (Fin r) (𝓞 L))) :=
    { toFun := fun g =>
        { toFun := fun B => Multiplicative.ofAdd ((g : Matrix (Fin n) (Fin n) (𝓞 L)) * Multiplicative.toAdd B)
          invFun := fun B => Multiplicative.ofAdd (((g⁻¹ : GL (Fin n) (𝓞 L)) : Matrix (Fin n) (Fin n) (𝓞 L)) *
            Multiplicative.toAdd B)
          left_inv := fun B => by simp [← Matrix.mul_assoc]
          right_inv := fun B => by simp [← Matrix.mul_assoc]
          map_mul' := fun B C => by simp [Matrix.mul_add] }
      map_one' := by ext B; simp
      map_mul' := fun g h => by ext B; simp [Matrix.mul_assoc] }
  let Φ₀ : Multiplicative (Matrix (Fin n) (Fin r) (𝓞 L)) ⋊[ψ] GL (Fin n) (𝓞 L) →*
      Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L) :=
    { toFun := fun p => Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (p.right : Matrix (Fin n) (Fin n) (𝓞 L)) (Multiplicative.toAdd p.left) 0 1)
      map_one' := by simp
      map_mul' := fun p q => by
        simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, Matrix.reindex_apply,
          Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
        congr 1
        simp [ψ, add_comm] }
  let Φ : Multiplicative (Matrix (Fin n) (Fin r) (𝓞 L)) ⋊[ψ] GL (Fin n) (𝓞 L) →* GL (Fin (n + r)) (𝓞 L) :=
    Φ₀.toHomUnits
  have hΦv : ∀ p, ((Φ p : GL (Fin (n + r)) (𝓞 L)) : Matrix (Fin (n + r)) (Fin (n + r)) (𝓞 L)) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (p.right : Matrix (Fin n) (Fin n) (𝓞 L)) (Multiplicative.toAdd p.left) 0 1) :=
    fun p => rfl
  have hinj : Function.Injective Φ := by
    intro p q hpq
    have h1 := congrArg Units.val hpq
    rw [hΦv, hΦv] at h1
    have h2 := (Matrix.reindex finSumFinEquiv finSumFinEquiv).injective h1
    rw [Matrix.fromBlocks_inj] at h2
    exact SemidirectProduct.ext h2.2.1 (Units.ext h2.1)
  choose B hB using hblock
  have hΦf : ∀ x, Φ ⟨Multiplicative.ofAdd (B x), f₀ x⟩ = f x := by
    intro x
    apply Units.ext
    rw [hΦv]
    exact (hB x).symm
  let f' : H →* Multiplicative (Matrix (Fin n) (Fin r) (𝓞 L)) ⋊[ψ] GL (Fin n) (𝓞 L) :=
    { toFun := fun x => ⟨Multiplicative.ofAdd (B x), f₀ x⟩
      map_one' := hinj (by rw [hΦf, map_one, map_one])
      map_mul' := fun x y => hinj (by rw [map_mul Φ, hΦf, hΦf, hΦf, map_mul f]) }
  let u : GL (Fin n) (𝓞 L) := Units.map (Matrix.scalar (Fin n) : 𝓞 L →+* Matrix (Fin n) (Fin n) (𝓞 L)).toMonoidHom v⁻¹
  have hu : ∀ g, g * u = u * g := by
    intro g
    apply Units.ext
    simp only [Units.val_mul, u, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    exact ((Matrix.scalar_commute _ (fun r' => Commute.all _ r') _).eq).symm
  let χ := (ψ u⁻¹).toMonoidHom
  have hχ : ∀ a, SemidirectProduct.inl (φ := ψ) (χ a) =
      (SemidirectProduct.inr (φ := ψ) u)⁻¹ * SemidirectProduct.inl (φ := ψ) a *
        SemidirectProduct.inr (φ := ψ) u := by
    intro a
    have := SemidirectProduct.inl_aut (φ := ψ) u⁻¹ a
    rw [inv_inv, (SemidirectProduct.inr (φ := ψ)).map_inv u] at this
    exact this
  have hχeq : (χ : Multiplicative (Matrix (Fin n) (Fin r) (𝓞 L)) → _) = mulV n r ↑v := by
    funext a
    simp [χ, ψ, u, mulV, Matrix.smul_eq_diagonal_mul]
  have hA : APoly (Multiplicative (Matrix (Fin n) (Fin r) (𝓞 L))) χ (k + 1) := by
    rw [hχeq]
    exact aPoly_mulV_of_unit_place_monomials_ne_one hSpan hEig hL (k + 1) v hv n r
  have hC : ColPoly (SemidirectProduct.rightHom (φ := ψ)) SemidirectProduct.inr u (k + 1) := by
    refine hTr _ _ _ _ _ (fun g => SemidirectProduct.rightHom_inr g) u hu SemidirectProduct.inl
      SemidirectProduct.inl_injective ?_ χ hχ (k + 1) hA
    intro x
    rw [SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
  have hs : ∀ g, SemidirectProduct.rightHom (φ := ψ) (SemidirectProduct.inr g) = g :=
    SemidirectProduct.rightHom_inr
  have hΦs : ∀ g, stab (𝓞 L) n (n + r) (Nat.le_add_right n r) g = Φ (SemidirectProduct.inr g) := by
    intro g
    apply Units.ext
    rw [hΦv]
    ext i j
    unfold stab padHom
    simp only [Units.coe_map, MonoidHom.coe_mk, OneHom.coe_mk]
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;>
      refine Fin.addCases (fun c => ?_) (fun d => ?_) j <;>
      simp [padMat, Matrix.reindex_apply, Matrix.one_apply, Fin.ext_iff]
    all_goals (intro h; first | (have := a.isLt; omega) | (have := c.isLt; omega))
  let w := cmap f' (k + 1) z
  have hw : IsCyc w := by
    unfold IsCyc at hz ⊢
    rw [hCh.2.1 H _ f' k z, hz, map_zero]
  have hb := H_affine_combination_eq_of_quadratic_relation hCh hSep hCore hEv _ _ hs u hu hC (j := k) le_rfl w hw
  have hf : f = Φ.comp f' := MonoidHom.ext fun x => (hΦf x).symm
  have e1 : cmap f (k + 1) z = cmap Φ (k + 1) w := by
    rw [hf, hCh.2.2.1]
  have e2 : cmap ((stab (𝓞 L) n (n + r) (Nat.le_add_right n r)).comp f₀) (k + 1) z =
      cmap Φ (k + 1) (cmap ((SemidirectProduct.inr (φ := ψ)).comp SemidirectProduct.rightHom) (k + 1) w) := by
    have hst : (stab (𝓞 L) n (n + r) (Nat.le_add_right n r)).comp f₀ =
        Φ.comp (((SemidirectProduct.inr (φ := ψ)).comp SemidirectProduct.rightHom).comp f') :=
      MonoidHom.ext fun x => hΦs (f₀ x)
    rw [hst, hCh.2.2.1, hCh.2.2.1]
  rw [e1, e2, ← map_sub]
  unfold IsBd at hb ⊢
  obtain ⟨y, hy⟩ := hb
  exact ⟨cmap Φ (k + 1 + 1) y, by rw [hCh.2.1, hy]⟩

end PositivityTheory.KB.SplitAffineSpectral

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.TransferAlt
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.TransferPrism
noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral.PrismTransfer

open PositivityTheory.KB.SplitAffineSpectral

variable {Y : Type}

theorem dc_cons {m : ℕ} (G : (Fin (m + 2) → Y) → ℝ) (a : Y) (t : Fin (m + 2) → Y) :
    dc G (Fin.cons a t) = G t - dc (fun z => G (Fin.cons a z)) t := by
  unfold dc
  rw [Fin.sum_univ_succ]
  have h0 : (fun j => (Fin.cons a t : Fin (m + 3) → Y) ((0 : Fin (m + 3)).succAbove j)) = t := by
    funext j; simp
  have hs : ∀ i : Fin (m + 2), (fun j => (Fin.cons a t : Fin (m + 3) → Y) (i.succ.succAbove j)) =
      Fin.cons a (fun j => t (i.succAbove j)) := by
    intro i; funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · simp [Fin.succ_succAbove_succ]
  rw [h0]
  simp only [hs, Fin.val_zero, pow_zero, one_mul, Fin.val_succ, pow_succ]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem dc_sub {m : ℕ} (G H : (Fin (m + 1) → Y) → ℝ) (x : Fin (m + 2) → Y) :
    dc (fun z => G z - H z) x = dc G x - dc H x := by
  unfold dc
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem dc1 (G : (Fin 1 → Y) → ℝ) (y : Fin 2 → Y) :
    dc G y = G (fun _ => y 1) - G (fun _ => y 0) := by
  unfold dc
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_zero]
  have h0 : (fun j : Fin 1 => y ((0 : Fin 2).succAbove j)) = fun _ => y 1 := by
    funext j; rw [Fin.fin_one_eq_zero j]; rfl
  have h1 : (fun j : Fin 1 => y ((Fin.succ 0 : Fin 2).succAbove j)) = fun _ => y 0 := by
    funext j; rw [Fin.fin_one_eq_zero j]; rfl
  rw [h0, h1]; simp; ring

def prism (φ : Y → Y) : (m : ℕ) → ((Fin (m + 2) → Y) → ℝ) → (Fin (m + 1) → Y) → ℝ
  | 0, F, x => F (Fin.cons (x 0) (φ ∘ x))
  | m + 1, F, x => F (Fin.cons (x 0) (φ ∘ x)) - prism φ m (fun z => F (Fin.cons (x 0) z)) (Fin.tail x)

theorem prism_sub (φ : Y → Y) : ∀ (m : ℕ) (F G : (Fin (m + 2) → Y) → ℝ) (x : Fin (m + 1) → Y),
    prism φ m (fun z => F z - G z) x = prism φ m F x - prism φ m G x
  | 0, F, G, x => rfl
  | m + 1, F, G, x => by
    simp only [prism]
    rw [prism_sub φ m]
    ring

theorem prism_zero (φ : Y → Y) : ∀ (m : ℕ) (x : Fin (m + 1) → Y),
    prism φ m (fun _ => (0 : ℝ)) x = 0
  | 0, x => rfl
  | m + 1, x => by
    simp only [prism]
    rw [prism_zero φ m]
    ring

theorem prism_base (φ : Y → Y) (F : (Fin 2 → Y) → ℝ) (x : Fin 2 → Y) :
    dc (prism φ 0 F) x + prism φ 1 (dc F) x = F (φ ∘ x) - F x := by
  obtain ⟨a, b, rfl⟩ : ∃ a b, x = Fin.cons a (fun _ : Fin 1 => b) := ⟨x 0, x 1, by
    funext j; refine Fin.cases rfl (fun k => ?_) j; rw [Fin.fin_one_eq_zero k]; rfl⟩
  simp only [prism, Fin.cons_zero, Fin.tail_cons]
  simp only [Fin.comp_cons]
  simp only [dc_cons, dc1]
  simp only [Fin.cons_zero, Fin.cons_one, Function.comp_def]
  ring

theorem prism_htpy (φ : Y → Y) : ∀ (m : ℕ) (F : (Fin (m + 2) → Y) → ℝ) (x : Fin (m + 2) → Y),
    dc (prism φ m F) x + prism φ (m + 1) (dc F) x = F (φ ∘ x) - F x := by
  intro m
  induction m with
  | zero => exact prism_base φ
  | succ m ih =>
    intro F x
    obtain ⟨a, t, rfl⟩ : ∃ a t, x = Fin.cons a t := ⟨x 0, Fin.tail x, (Fin.cons_self_tail x).symm⟩
    rw [dc_cons]
    have hK : (fun z => prism φ (m + 1) F (Fin.cons a z)) =
        fun z => F (Fin.cons a (Fin.cons (φ a) (φ ∘ z))) - prism φ m (fun w => F (Fin.cons a w)) z := by
      funext z; simp only [prism, Fin.cons_zero, Fin.tail_cons, Fin.comp_cons]
    rw [hK, dc_sub]
    have h2 : prism φ (m + 2) (dc F) (Fin.cons a t) =
        dc F (Fin.cons a (φ ∘ Fin.cons a t)) - prism φ (m + 1) (fun z => dc F (Fin.cons a z)) t := by
      simp only [prism, Fin.cons_zero, Fin.tail_cons]
    rw [h2]
    have h3 : (fun z => dc F (Fin.cons a z)) = fun z => F z - dc (fun w => F (Fin.cons a w)) z := by
      funext z; exact dc_cons F a z
    rw [h3, prism_sub, Fin.comp_cons, dc_cons, dc_cons]
    have h4 : dc (fun z => F (Fin.cons a (Fin.cons (φ a) (φ ∘ z)))) t =
        dc (fun w => F (Fin.cons a (Fin.cons (φ a) w))) (φ ∘ t) := rfl
    rw [h4]
    linarith [ih (fun z => F (Fin.cons a z)) t]

theorem prism_smul {P : Type} [Group P] (φ : P → P) (k : P) (hφ : ∀ y, φ (k * y) = k * φ y) :
    ∀ (m : ℕ) (F : (Fin (m + 2) → P) → ℝ) (x : Fin (m + 1) → P),
      prism φ m F (fun i => k * x i) = prism φ m (fun z => F (fun i => k * z i)) x
  | 0, F, x => by
    simp only [prism]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp [hφ]
  | m + 1, F, x => by
    simp only [prism]
    have e1 : (Fin.cons (k * x 0) (φ ∘ fun i => k * x i) : Fin (m + 3) → P) =
        fun i => k * (Fin.cons (x 0) (φ ∘ x) : Fin (m + 3) → P) i := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp [hφ]
    rw [e1]
    congr 1
    have e2 : (Fin.tail fun i => k * x i) = fun i => k * Fin.tail x i := rfl
    rw [e2, prism_smul φ k hφ m]
    congr 1
    funext z
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp

end PositivityTheory.KB.SplitAffineSpectral.PrismTransfer

end
end

noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral.PrismTransfer

open PositivityTheory.KB.SplitAffineSpectral Polynomial

theorem pow_intertwine {V W : Type} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (T : Module.End ℝ V) (T' : Module.End ℝ W) (L : V →ₗ[ℝ] W) (h : ∀ v, T' (L v) = L (T v)) :
    ∀ (n : ℕ) (v : V), (T' ^ n) (L v) = L ((T ^ n) v)
  | 0, v => rfl
  | n + 1, v => by
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, h, pow_intertwine T T' L h n]

theorem aeval_intertwine {V W : Type} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (T : Module.End ℝ V) (T' : Module.End ℝ W) (L : V →ₗ[ℝ] W) (h : ∀ v, T' (L v) = L (T v))
    (f : ℝ[X]) (v : V) : aeval T' f (L v) = L (aeval T f v) := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), LinearMap.add_apply, hp, hq]
  | monomial n a =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      pow_intertwine T T' L h n, map_smul]

theorem pow_mem {V : Type} [AddCommGroup V] [Module ℝ V] (T : Module.End ℝ V) (S : Submodule ℝ V)
    (hT : ∀ v ∈ S, T v ∈ S) : ∀ (n : ℕ) (v : V), v ∈ S → (T ^ n) v ∈ S
  | 0, v, hv => hv
  | n + 1, v, hv => by
    rw [pow_succ, Module.End.mul_apply]
    exact pow_mem T S hT n _ (hT v hv)

theorem aeval_mem {V : Type} [AddCommGroup V] [Module ℝ V] (T : Module.End ℝ V) (S : Submodule ℝ V)
    (hT : ∀ v ∈ S, T v ∈ S) (f : ℝ[X]) (v : V) (hv : v ∈ S) : aeval T f v ∈ S := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), LinearMap.add_apply]; exact S.add_mem hp hq
  | monomial n a =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact S.smul_mem a (pow_mem T S hT n v hv)

def invSub {P : Type} [Group P] (S : Set P) (m : ℕ) : Submodule ℝ ((Fin m → P) → ℝ) where
  carrier := {F | InvS S F}
  add_mem' {F G} hF hG g hg y := by simp only [Pi.add_apply, hF g hg y, hG g hg y]
  zero_mem' g _ y := rfl
  smul_mem' r F hF g hg y := by simp only [Pi.smul_apply, hF g hg y]

def dcL (Y : Type) (m : ℕ) : ((Fin (m + 1) → Y) → ℝ) →ₗ[ℝ] ((Fin (m + 2) → Y) → ℝ) where
  toFun := dc
  map_add' F G := by
    funext y; simp only [dc, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' r F := by
    funext y; simp only [dc, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

def pullL {X Y : Type} (g : X → Y) (m : ℕ) : ((Fin m → Y) → ℝ) →ₗ[ℝ] ((Fin m → X) → ℝ) where
  toFun F x := F fun i => g (x i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end PositivityTheory.KB.SplitAffineSpectral.PrismTransfer

namespace PositivityTheory.KB.SplitAffineSpectral

open PrismTransfer Polynomial

theorem transfer : Transfer := by
  intro P Q A _ _ _ pr s hs u hu ι hι hran φ hφ m hA q hq
  obtain ⟨f, hf1, hfA⟩ := hA q hq
  refine ⟨f, hf1, fun c hc hcc => ?_⟩
  set t := s u with ht
  have hker : ∀ k : P, k ∈ (pr.ker : Set P) ↔ pr k = 1 := fun k => MonoidHom.mem_ker

  let ρ : P → P := fun y => y * (s (pr y))⁻¹
  have hρk : ∀ y, ∃ a, ι a = ρ y := fun y => (hran _).1 (by simp [ρ, hs])
  let ρA : P → A := fun y => Classical.choose (hρk y)
  have hρA : ∀ y, ι (ρA y) = ρ y := fun y => Classical.choose_spec (hρk y)
  have hιk : ∀ b, pr (ι b) = 1 := fun b => (hran _).2 ⟨b, rfl⟩
  have hρmul : ∀ k y, pr k = 1 → ρ (k * y) = k * ρ y := by
    intro k y hk; simp only [ρ, map_mul, hk, one_mul, mul_assoc]
  have hρAmul : ∀ b y, ρA (ι b * y) = b * ρA y := by
    intro b y; apply hι; rw [map_mul, hρA, hρA, hρmul _ _ (hιk b)]
  have hcomm : ∀ g : Q, s g * t = t * s g := by
    intro g; rw [ht, ← map_mul, ← map_mul, hu]
  have hρconj : ∀ y, ρ (t⁻¹ * y * t) = t⁻¹ * ρ y * t := by
    intro y
    have hp : pr (t⁻¹ * y * t) = pr y := by
      rw [map_mul, map_mul, map_inv, ht, hs, hu, mul_inv_cancel_left]
    have hc' : (s (pr y))⁻¹ * t = t * (s (pr y))⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hcomm, mul_assoc, mul_inv_cancel, mul_one]
    show t⁻¹ * y * t * (s (pr (t⁻¹ * y * t)))⁻¹ = t⁻¹ * (y * (s (pr y))⁻¹) * t
    rw [hp]
    simp only [mul_assoc, hc']
  have hρAconj : ∀ y, ρA (t⁻¹ * y * t) = φ (ρA y) := by
    intro y; apply hι; rw [hρA, hρconj, hφ, hρA]

  let cA : (Fin (q + 2) → A) → ℝ := fun x => c fun i => ι (x i)
  have hcA : InvS Set.univ cA := by
    intro b _ x
    simp only [cA, map_mul]
    exact hc (ι b) ((hker _).2 (hιk b)) _
  have hccA : dc cA = 0 := by
    funext x
    have := congrFun hcc (fun i => ι (x i))
    simpa [dc, cA] using this
  obtain ⟨eA, heA, hfe⟩ := hfA cA hcA hccA

  let T : (n : ℕ) → Module.End ℝ ((Fin n → P) → ℝ) := fun n => mapOp (fun y => t⁻¹ * y * t) n
  have hTR : ∀ (n : ℕ) (g : (Fin n → A) → ℝ),
      T n (pullL ρA n g) = pullL ρA n (mapOp φ n g) := by
    intro n g; funext y; simp only [T, mapOp, pullL, LinearMap.coe_mk, AddHom.coe_mk, hρAconj]
  have hTd : ∀ (n : ℕ) (F : (Fin (n + 1) → P) → ℝ), T (n + 2) (dcL P n F) = dcL P n (T (n + 1) F) :=
    fun n F => rfl
  have hRd : ∀ (n : ℕ) (g : (Fin (n + 1) → A) → ℝ), pullL ρA (n + 2) (dcL A n g) = dcL P n (pullL ρA (n + 1) g) :=
    fun n g => rfl

  have hpr : c = pullL ρA (q + 2) cA - dc (prism ρ q c) := by
    funext y
    have h1 := prism_htpy ρ q c y
    rw [hcc] at h1
    have h0 : prism ρ (q + 1) (fun _ => (0 : ℝ)) y = 0 := prism_zero ρ (q + 1) y
    have h2 : pullL ρA (q + 2) cA y = c (ρ ∘ y) := by
      simp only [pullL, cA, LinearMap.coe_mk, AddHom.coe_mk, hρA]; rfl
    simp only [Pi.sub_apply, h2]
    have h3 : (0 : (Fin (q + 3) → P) → ℝ) = fun _ => 0 := rfl
    rw [h3, h0] at h1
    linarith

  have hprismInv : InvS (pr.ker : Set P) (prism ρ q c) := by
    intro k hk y
    rw [prism_smul ρ k (fun y => hρmul k y ((hker k).1 hk)) q c y]
    congr 1
    funext z
    exact hc k hk z
  have hTinv : ∀ (n : ℕ), ∀ F ∈ invSub (pr.ker : Set P) n, T n F ∈ invSub (pr.ker : Set P) n := by
    intro n F hF k hk y
    simp only [T, mapOp, LinearMap.coe_mk, AddHom.coe_mk]
    have hk' : t⁻¹ * k * t ∈ (pr.ker : Set P) := by
      rw [hker] at hk ⊢
      rw [map_mul, map_mul, hk, mul_one, map_inv, inv_mul_cancel]
    have := hF _ hk' (fun i => t⁻¹ * y i * t)
    simp only [mul_assoc, mul_inv_cancel_left] at this ⊢
    exact this
  refine ⟨pullL ρA (q + 1) eA - aeval (T (q + 1)) f (prism ρ q c), ?_, ?_⟩
  · intro k hk y
    obtain ⟨b, rfl⟩ := (hran k).1 ((hker k).1 hk)
    have h1 : aeval (T (q + 1)) f (prism ρ q c) ∈ invSub (pr.ker : Set P) (q + 1) :=
      aeval_mem _ _ (hTinv (q + 1)) f _ hprismInv
    simp only [Pi.sub_apply]
    rw [h1 (ι b) hk y]
    congr 1
    simp only [pullL, LinearMap.coe_mk, AddHom.coe_mk, hρAmul]
    exact heA b trivial _
  · have e1 : aeval (T (q + 2)) f c =
        aeval (T (q + 2)) f (pullL ρA (q + 2) cA) - aeval (T (q + 2)) f (dcL P q (prism ρ q c)) := by
      conv_lhs => rw [hpr]
      rw [map_sub]
      rfl
    change aeval (T (q + 2)) f c = _
    rw [e1, aeval_intertwine (mapOp φ (q + 2)) (T (q + 2)) (pullL ρA (q + 2)) (hTR (q + 2)),
      aeval_intertwine (T (q + 1)) (T (q + 2)) (dcL P q) (hTd q), hfe]
    rw [show dc eA = dcL A q eA from rfl, hRd]
    rw [← map_sub]
    rfl

end PositivityTheory.KB.SplitAffineSpectral

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.ProdEmbNeOne
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.EigenKill
noncomputable section

open Polynomial

namespace PositivityTheory.KB.SplitAffineSpectral.EigenLocalizationShapes

def gpoly (Λ : ℂ) : ℝ[X] := X ^ 2 - C (2 * Λ.re) * X + C (Complex.normSq Λ)

theorem gpoly_eval_one (Λ : ℂ) : (gpoly Λ).eval 1 = Complex.normSq (1 - Λ) := by
  simp only [gpoly, eval_add, eval_sub, eval_pow, eval_X, eval_mul, eval_C, Complex.normSq_apply,
    Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
  ring

theorem mapOp_apply {A : Type} (φ : A → A) (m : ℕ) (F : (Fin m → A) → ℝ) (y : Fin m → A) :
    mapOp φ m F y = F fun i => φ (y i) := rfl

theorem kill_one {A : Type} (φ : A → A) (m : ℕ) (E : (Fin m → A) → ℂ) (Λ z : ℂ)
    (hE : ∀ y, E (fun i => φ (y i)) = Λ * E y) :
    aeval (mapOp φ m) (gpoly Λ) (fun y => (z * E y).re) = 0 := by
  simp only [gpoly, map_add (f := _), map_sub, map_mul, aeval_X, aeval_C, map_pow]
  funext y
  simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply, pow_two,
    Module.algebraMap_end_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mapOp_apply,
    hE, Pi.zero_apply]
  simp only [Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

theorem kill_sum {A : Type} (φ : A → A) (m : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (E : ι → (Fin m → A) → ℂ) (Λ z : ι → ℂ) (hE : ∀ j y, E j (fun i => φ (y i)) = Λ j * E j y)
    (F : (Fin m → A) → ℝ) (hF : ∀ y, (F y : ℂ) = ∑ j, z j * E j y) :
    aeval (mapOp φ m) (∏ j, gpoly (Λ j)) F = 0 := by
  have hF' : F = ∑ j, fun y => (z j * E j y).re := by
    funext y
    rw [Finset.sum_apply, ← Complex.re_sum, ← hF y, Complex.ofReal_re]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hF', map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), map_mul, Module.End.mul_apply,
    kill_one φ m (E j) (Λ j) (z j) (hE j), map_zero]

theorem cup_kill {A : Type} [Group A] (φ : A →* A) {ι : Type} [Fintype ι] [DecidableEq ι]
    (β : ι → Additive A → ℂ) (lam : ι → ℂ)
    (hβ : ∀ j x, β j (Additive.ofMul (φ x)) = lam j * β j (Additive.ofMul x))
    (hspan : ∀ α : Additive A →+ ℝ, ∃ c : ι → ℂ, ∀ x, (α x : ℂ) = ∑ j, c j * β j x) (q : ℕ)
    (α : Fin (q + 1) → (Additive A →+ ℝ)) :
    aeval (mapOp φ (q + 2)) (∏ J : Fin (q + 1) → ι, gpoly (∏ i, lam (J i))) (cupH α) = 0 := by
  choose c hc using hspan
  let d : Fin (q + 1) → (Fin (q + 2) → A) → Additive A :=
    fun i y => Additive.ofMul ((y i.castSucc)⁻¹ * y i.succ)
  let E : (Fin (q + 1) → ι) → (Fin (q + 2) → A) → ℂ := fun J y => ∏ i, β (J i) (d i y)
  let Λ : (Fin (q + 1) → ι) → ℂ := fun J => ∏ i, lam (J i)
  let z : (Fin (q + 1) → ι) → ℂ := fun J => ∏ i, c (α i) (J i)
  have hE : ∀ J y, E J (fun i => φ (y i)) = Λ J * E J y := by
    intro J y
    simp only [E, Λ]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    have : d i (fun k => φ (y k)) = Additive.ofMul (φ ((y i.castSucc)⁻¹ * y i.succ)) := by
      simp only [d, map_mul, map_inv]
    rw [this, hβ]
  have hF : ∀ y, (cupH α y : ℂ) = ∑ J, z J * E J y := by
    intro y
    have h1 : (cupH α y : ℂ) = ∏ i, ∑ j, c (α i) j * β j (d i y) := by
      rw [cupH, Complex.ofReal_prod]
      exact Finset.prod_congr rfl fun i _ => hc (α i) _
    rw [h1, Finset.prod_univ_sum, Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun J _ => ?_
    simp only [z, E]
    rw [Finset.prod_mul_distrib]
  exact kill_sum (⇑φ) (q + 2) E Λ z hE (cupH α) hF

end PositivityTheory.KB.SplitAffineSpectral.EigenLocalizationShapes
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.EigenSpan
noncomputable section

open NumberField

namespace PositivityTheory.KB.SplitAffineSpectral.EigenLocalizationShapes

variable (L : Type) [Field L] [NumberField L]

def embLin (σ : L →+* ℂ) : 𝓞 L →ₗ[ℤ] ℂ := (σ.comp (algebraMap (𝓞 L) L)).toAddMonoidHom.toIntLinearMap

def coeLin : (𝓞 L →ₗ[ℤ] ℂ) →ₗ[ℂ] (𝓞 L → ℂ) where
  toFun f := ⇑f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem embLin_linIndep : LinearIndependent ℂ (embLin L) := by
  have hinj : Function.Injective
      (fun σ : L →+* ℂ => ((σ.comp (algebraMap (𝓞 L) L)).toMonoidHom : 𝓞 L →* ℂ)) := by
    intro σ τ h
    apply IsFractionRing.ringHom_ext (A := 𝓞 L)
    intro x
    exact DFunLike.congr_fun h x
  have h1 := (linearIndependent_monoidHom (𝓞 L) ℂ).comp _ hinj
  apply LinearIndependent.of_comp (coeLin L)
  exact h1

theorem finrank_lin : Module.finrank ℂ (𝓞 L →ₗ[ℤ] ℂ) = Fintype.card (L →+* ℂ) := by
  rw [Module.finrank_linearMap_self, NumberField.RingOfIntegers.rank, NumberField.Embeddings.card]

theorem emb_span (α : 𝓞 L →+ ℝ) :
    ∃ c : (L →+* ℂ) → ℂ, ∀ x : 𝓞 L, (α x : ℂ) = ∑ σ, c σ * σ (algebraMap (𝓞 L) L x) := by
  have hspan := (embLin_linIndep L).span_eq_top_of_card_eq_finrank' (finrank_lin L).symm
  let f : 𝓞 L →ₗ[ℤ] ℂ := ((Complex.ofRealHom : ℝ →+* ℂ).toAddMonoidHom.comp α).toIntLinearMap
  have hf : f ∈ Submodule.span ℂ (Set.range (embLin L)) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hf
  refine ⟨c, fun x => ?_⟩
  have hx := LinearMap.congr_fun hc x
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at hx
  exact hx.symm

theorem mat_span (n r : ℕ) (α : Additive (Multiplicative (Matrix (Fin n) (Fin r) (𝓞 L))) →+ ℝ) :
    ∃ c : Fin n × Fin r × (L →+* ℂ) → ℂ, ∀ x,
      (α x : ℂ) = ∑ j, c j * j.2.2 (algebraMap (𝓞 L) L
        (Multiplicative.toAdd (Additive.toMul x) j.1 j.2.1)) := by
  let e : Matrix (Fin n) (Fin r) (𝓞 L) →+ Additive (Multiplicative (Matrix (Fin n) (Fin r) (𝓞 L))) :=
    { toFun := fun m => Additive.ofMul (Multiplicative.ofAdd m)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hc : ∀ i j, ∃ c : (L →+* ℂ) → ℂ, ∀ y : 𝓞 L,
      ((α.comp (e.comp (Matrix.singleAddMonoidHom i j))) y : ℂ) =
        ∑ σ, c σ * σ (algebraMap (𝓞 L) L y) :=
    fun i j => emb_span L _
  choose c hc using hc
  refine ⟨fun j => c j.1 j.2.1 j.2.2, fun x => ?_⟩
  have lhs : (α x : ℂ) = ∑ i, ∑ j, ((α.comp (e.comp (Matrix.singleAddMonoidHom i j)))
      (Multiplicative.toAdd (Additive.toMul x) i j) : ℂ) := by
    have hx : x = e (Multiplicative.toAdd (Additive.toMul x)) := rfl
    conv_lhs => rw [hx, Matrix.matrix_eq_sum_single (Multiplicative.toAdd (Additive.toMul x))]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, Complex.ofReal_sum]
    rfl
  rw [lhs]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact hc i j _

end PositivityTheory.KB.SplitAffineSpectral.EigenLocalizationShapes
end
end

noncomputable section

open NumberField InfinitePlace Polynomial

namespace PositivityTheory.KB.SplitAffineSpectral.EigenLocalizationShapes

def mulVHom {L : Type} [Field L] [NumberField L] (n r : ℕ) (v : 𝓞 L) :
    Multiplicative (Matrix (Fin n) (Fin r) (𝓞 L)) →* Multiplicative (Matrix (Fin n) (Fin r) (𝓞 L)) where
  toFun := mulV n r v
  map_one' := by simp [mulV]
  map_mul' x y := by simp [mulV, smul_add]

theorem prod_emb_ne_one {L : Type} [Field L] [NumberField L] (m : ℕ) (v : (𝓞 L)ˣ)
    (hv : ∀ a : InfinitePlace L → ℕ, 0 < ∑ w, a w → ∑ w, a w ≤ m → ∏ w, (w (v : L)) ^ a w ≠ 1)
    (q : ℕ) (hq : q + 1 ≤ m) (σs : Fin (q + 1) → (L →+* ℂ)) :
    ∏ i, σs i (algebraMap (𝓞 L) L (v : 𝓞 L)) ≠ 1 := by
  classical
  intro h
  have hn : ∏ i, (InfinitePlace.mk (σs i)) (algebraMap (𝓞 L) L (v : 𝓞 L)) = 1 := by
    have := congrArg norm h
    rw [norm_prod, norm_one] at this
    simpa [InfinitePlace.apply] using this
  let g : Fin (q + 1) → InfinitePlace L := fun i => InfinitePlace.mk (σs i)
  let a : InfinitePlace L → ℕ := fun w => (Finset.univ.filter fun i => g i = w).card
  have hsum : ∑ w, a w = q + 1 := by
    have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin (q + 1))))
      (t := (Finset.univ : Finset (InfinitePlace L))) (f := g) (fun _ _ => Finset.mem_univ _)
    simpa [a] using this.symm
  have hprod : ∏ w, (w (algebraMap (𝓞 L) L (v : 𝓞 L))) ^ a w = 1 := by
    rw [← hn, ← Finset.prod_fiberwise Finset.univ g]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [Finset.prod_congr rfl (g := fun _ => w (algebraMap (𝓞 L) L (v : 𝓞 L))), Finset.prod_const]
    intro i hi
    have hgi : g i = w := (Finset.mem_filter.mp hi).2
    simp only [g] at hgi
    rw [hgi]
  exact hv a (by omega) (by omega) hprod

end PositivityTheory.KB.SplitAffineSpectral.EigenLocalizationShapes

open PositivityTheory.KB.SplitAffineSpectral.EigenLocalizationShapes in
theorem PositivityTheory.KB.SplitAffineSpectral.eigen : PositivityTheory.KB.SplitAffineSpectral.Eigen := by
  intro L _ _ _ m v hv n r q hq
  classical
  let lam : Fin n × Fin r × (L →+* ℂ) → ℂ := fun j => j.2.2 (algebraMap (𝓞 L) L (v : 𝓞 L))
  let β : Fin n × Fin r × (L →+* ℂ) → Additive (Multiplicative (Matrix (Fin n) (Fin r) (𝓞 L))) → ℂ :=
    fun j x => j.2.2 (algebraMap (𝓞 L) L (Multiplicative.toAdd (Additive.toMul x) j.1 j.2.1))
  refine ⟨∏ J : Fin (q + 1) → Fin n × Fin r × (L →+* ℂ), gpoly (∏ i, lam (J i)), ?_, ?_⟩
  · rw [Polynomial.eval_prod]
    refine Finset.prod_ne_zero_iff.mpr fun J _ => ?_
    rw [gpoly_eval_one, Ne, Complex.normSq_eq_zero, sub_eq_zero]
    exact fun h => prod_emb_ne_one m v hv q hq (fun i => (J i).2.2) h.symm
  · intro α
    have hβ : ∀ j x, β j (Additive.ofMul (mulVHom n r (v : 𝓞 L) x)) = lam j * β j (Additive.ofMul x) := by
      intro j x
      change j.2.2 (algebraMap (𝓞 L) L (Multiplicative.toAdd (mulV n r (v : 𝓞 L) x) j.1 j.2.1)) =
        j.2.2 (algebraMap (𝓞 L) L (v : 𝓞 L)) * j.2.2 (algebraMap (𝓞 L) L (Multiplicative.toAdd x j.1 j.2.1))
      simp only [mulV, toAdd_ofAdd, Matrix.smul_apply, smul_eq_mul, map_mul]
    exact cup_kill (mulVHom n r (v : 𝓞 L)) β lam hβ (fun α => mat_span L n r α) q α
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.LcharKerNotFiniteIndex
noncomputable section

open NumberField InfinitePlace Pointwise

namespace PositivityTheory.KB.SplitAffineSpectral.unitAtAlt

variable {L : Type} [Field L] [NumberField L]

omit [NumberField L] in
theorem place_pos (v : (𝓞 L)ˣ) (w : InfinitePlace L) : 0 < w (algebraMap (𝓞 L) L (v : 𝓞 L)) := w.pos_iff.mpr (by simp)

def lchar (a : InfinitePlace L → ℕ) : (𝓞 L)ˣ →* Multiplicative ℝ where
  toFun v := Multiplicative.ofAdd (∑ w, (a w : ℝ) * Real.log (w (algebraMap (𝓞 L) L (v : 𝓞 L))))
  map_one' := by simp
  map_mul' x y := by
    rw [← ofAdd_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Units.val_mul, map_mul, map_mul, Real.log_mul (place_pos x w).ne' (place_pos y w).ne']
    ring

theorem lchar_eq_one_iff (a : InfinitePlace L → ℕ) (v : (𝓞 L)ˣ) :
    lchar a v = 1 ↔ ∏ w, (w (algebraMap (𝓞 L) L (v : 𝓞 L))) ^ a w = 1 := by
  have hpos : ∀ w : InfinitePlace L, 0 < w (algebraMap (𝓞 L) L (v : 𝓞 L)) ^ a w :=
    fun w => pow_pos (place_pos v w) _
  have hP : 0 < ∏ w, w (algebraMap (𝓞 L) L (v : 𝓞 L)) ^ a w :=
    Finset.prod_pos fun w _ => hpos w
  have hlog : Real.log (∏ w, w (algebraMap (𝓞 L) L (v : 𝓞 L)) ^ a w) =
      ∑ w, (a w : ℝ) * Real.log (w (algebraMap (𝓞 L) L (v : 𝓞 L))) := by
    rw [Real.log_prod (fun w _ => (hpos w).ne')]
    exact Finset.sum_congr rfl fun w _ => Real.log_pow _ _
  change Multiplicative.ofAdd (∑ w, (a w : ℝ) * Real.log (w (algebraMap (𝓞 L) L (v : 𝓞 L)))) = 1 ↔ _
  rw [ofAdd_eq_one, ← hlog]
  constructor
  · intro h
    rw [← Real.exp_log hP, h, Real.exp_zero]
  · intro h
    rw [h, Real.log_one]

theorem lchar_nontrivial (hC : IsTotallyComplex L) (a : InfinitePlace L → ℕ) (ha : 0 < ∑ w, a w)
    (hm : ∑ w, a w < nrComplexPlaces L) : ∃ v, lchar a v ≠ 1 := by
  classical
  have hcard : ∑ w, a w < Fintype.card (InfinitePlace L) := by
    rw [card_eq_nrRealPlaces_add_nrComplexPlaces]
    omega
  obtain ⟨w₁, hw₁⟩ : ∃ w₁, a w₁ = 0 := by
    by_contra h
    push_neg at h
    have h1 : ∑ _w : InfinitePlace L, 1 ≤ ∑ w, a w :=
      Finset.sum_le_sum fun w _ => Nat.one_le_iff_ne_zero.mpr (h w)
    simp at h1
    omega
  obtain ⟨w₂, hw₂⟩ : ∃ w₂, 0 < a w₂ := by
    by_contra h
    push_neg at h
    have h0 : ∑ w, a w = 0 := Finset.sum_eq_zero fun w _ => by
      have := h w
      omega
    omega
  have hne : w₂ ≠ w₁ := by
    rintro rfl
    omega
  obtain ⟨u, hu⟩ := NumberField.Units.dirichletUnitTheorem.exists_unit L w₁
  refine ⟨u, fun h => ?_⟩
  change Multiplicative.ofAdd (∑ w, (a w : ℝ) * Real.log (w (algebraMap (𝓞 L) L (u : 𝓞 L)))) = 1 at h
  rw [ofAdd_eq_one] at h
  have hlt : ∑ w, (a w : ℝ) * Real.log (w (algebraMap (𝓞 L) L (u : 𝓞 L))) <
      ∑ _w : InfinitePlace L, (0 : ℝ) := by
    apply Finset.sum_lt_sum
    · intro w _
      by_cases hw : w = w₁
      · subst hw
        simp [hw₁]
      · exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (hu w hw).le
    · exact ⟨w₂, Finset.mem_univ _,
        mul_neg_of_pos_of_neg (by exact_mod_cast hw₂) (hu w₂ hne)⟩
  rw [Finset.sum_const_zero, h] at hlt
  exact lt_irrefl _ hlt

theorem lchar_ker_not_finiteIndex (hC : IsTotallyComplex L) (a : InfinitePlace L → ℕ) (ha : 0 < ∑ w, a w)
    (hm : ∑ w, a w < nrComplexPlaces L) : ¬ (lchar a).ker.FiniteIndex := by
  intro hfi
  obtain ⟨v, hv⟩ := lchar_nontrivial hC a ha hm
  apply hv
  have hmem := (lchar a).ker.pow_index_mem v
  rw [MonoidHom.mem_ker, map_pow] at hmem
  have hidx : (lchar a).ker.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have h1 : Multiplicative.toAdd (lchar a v ^ (lchar a).ker.index) = 0 := by
    rw [hmem]
    rfl
  rw [toAdd_pow, nsmul_eq_mul, mul_eq_zero] at h1
  rcases h1 with h1 | h1
  · exact absurd (by exact_mod_cast h1) hidx
  · exact toAdd_eq_zero.mp h1

end PositivityTheory.KB.SplitAffineSpectral.unitAtAlt

open PositivityTheory.KB.SplitAffineSpectral.unitAtAlt in
theorem PositivityTheory.KB.SplitAffineSpectral.unit : PositivityTheory.KB.SplitAffineSpectral.Unit := by
  unfold PositivityTheory.KB.SplitAffineSpectral.Unit
  intro L _ _ hC m hm
  classical
  by_contra hcon
  push_neg at hcon
  let s : Finset (InfinitePlace L → ℕ) :=
    (Fintype.piFinset fun _ => Finset.range (m + 1)).filter
      fun a => 0 < ∑ w, a w ∧ ∑ w, a w ≤ m
  obtain ⟨k, hk, hfi⟩ := Subgroup.exists_finiteIndex_of_leftCoset_cover
    (H := fun a => (lchar a).ker) (g := fun _ => 1) (s := s) (by
      ext v
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true, one_smul]
      obtain ⟨a, ha0, ham, hprod⟩ := hcon v
      refine ⟨a, ?_, ?_⟩
      · simp only [s, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
        refine ⟨fun w => ?_, ha0, ham⟩
        have := Finset.single_le_sum (f := a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ w)
        omega
      · exact (MonoidHom.mem_ker).mpr ((lchar_eq_one_iff a v).mpr hprod))
  simp only [s, Finset.mem_filter] at hk
  exact lchar_ker_not_finiteIndex hC k hk.2.1 (lt_of_le_of_lt hk.2.2 hm) hfi
end
end

namespace PositivityTheory.KB

theorem sAff_of (hCh : SChain) (_hEv : SEv) (hSep : SSep) (_hBr : SBridge) : SAff :=
  SplitAffineSpectral.sAff_of_parts hCh hSep SplitAffineSpectral.core SplitAffineSpectral.transfer SplitAffineSpectral.span SplitAffineSpectral.unit SplitAffineSpectral.eigen
    SplitAffineSpectral.evCob

end PositivityTheory.KB
