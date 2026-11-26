module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.InflFacts

@[expose] public section
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.FinAct
noncomputable section

open MeasureTheory NumberField IsDedekindDomain ValuativeRel Matrix GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Geo (incFin galFin)
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DZA UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.L.FiniteActions

section Gen

variable {G H Γ V : Type} [Group G] [Group H] [Group Γ] [AddCommGroup V] [Module ℂ V]

private theorem mem_fx (ρ : Representation ℂ G V) (U : Subgroup G) (v : V) :
    v ∈ fixed ρ U ↔ ∀ u ∈ U, ρ u v = v := by
  show (∀ h : U, ρ h v = ((1 : U →* ℂˣ) h : ℂ) • v) ↔ _
  simp only [MonoidHom.one_apply, Units.val_one, one_smul]
  exact ⟨fun h u hu => h ⟨u, hu⟩, fun h u => h u u.2⟩

private theorem fx_stable (ρ : Representation ℂ G V) (ι : H →* G) (p : H →* Γ) (y : H) {v : V}
    (hv : v ∈ fixed ρ (p.ker.map ι)) : ρ (ι y) v ∈ fixed ρ (p.ker.map ι) := by
  rw [mem_fx] at hv ⊢
  rintro u ⟨k, hk, rfl⟩
  have hk0 : p k = 1 := hk
  have hk' : y⁻¹ * k * y ∈ p.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, hk0, mul_one, map_inv, inv_mul_cancel]
  have hfix := hv _ ⟨_, hk', rfl⟩
  calc ρ (ι k) (ρ (ι y) v) = ρ (ι (k * y)) v := by rw [map_mul ι, map_mul ρ, Module.End.mul_apply]
    _ = ρ (ι (y * (y⁻¹ * k * y))) v := by congr 2; group
    _ = ρ (ι y) (ρ (ι (y⁻¹ * k * y)) v) := by rw [map_mul ι y, map_mul ρ, Module.End.mul_apply]
    _ = ρ (ι y) v := by rw [hfix]

private theorem fx_eq (ρ : Representation ℂ G V) (ι : H →* G) (p : H →* Γ) {y y' : H} (h : p y = p y')
    {v : V} (hv : v ∈ fixed ρ (p.ker.map ι)) : ρ (ι y) v = ρ (ι y') v := by
  rw [mem_fx] at hv
  have hk : y'⁻¹ * y ∈ p.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  have hfix := hv _ ⟨_, hk, rfl⟩
  calc ρ (ι y) v = ρ (ι (y' * (y'⁻¹ * y))) v := by rw [mul_inv_cancel_left]
    _ = ρ (ι y') (ρ (ι (y'⁻¹ * y)) v) := by rw [map_mul ι, map_mul ρ, Module.End.mul_apply]
    _ = ρ (ι y') v := by rw [hfix]

private def rp (ρ : Representation ℂ G V) (ι : H →* G) (p : H →* Γ) (hp : Function.Surjective p) :
    Representation ℂ Γ (fixed ρ (p.ker.map ι)) where
  toFun g := (ρ (ι (Function.surjInv hp g))).restrict fun _ hv => fx_stable ρ ι p _ hv
  map_one' := by
    ext ⟨v, hv⟩
    have h : p (Function.surjInv hp 1) = p 1 := by simp [Function.surjInv_eq]
    simpa using fx_eq ρ ι p h hv
  map_mul' a b := by
    ext ⟨v, hv⟩
    have h : p (Function.surjInv hp (a * b)) = p (Function.surjInv hp a * Function.surjInv hp b) := by
      simp [Function.surjInv_eq]
    simpa using fx_eq ρ ι p h hv

private theorem rp_spec (ρ : Representation ℂ G V) (ι : H →* G) (p : H →* Γ) (hp : Function.Surjective p)
    (y : H) (x : fixed ρ (p.ker.map ι)) : (rp ρ ι p hp (p y) x : V) = ρ (ι y) x := by
  show ρ (ι (Function.surjInv hp (p y))) x = _
  exact fx_eq ρ ι p (Function.surjInv_eq hp (p y)) x.2

private theorem rel_eq (ι : H →* G) (hι : Function.Injective ι) (p : H →* Γ) (hp : Function.Surjective p) :
    (p.ker.map ι).relIndex ι.range = Nat.card Γ := by
  rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map_of_injective _ _ hι, Subgroup.relIndex_top_right,
    Subgroup.index_ker, MonoidHom.range_eq_top.mpr hp]
  exact Subgroup.card_top

private theorem lev_eq_lemma (ι : H →* G) (hι : Function.Injective ι) (p : H →* Γ) (a b : H) :
    ((ι a : G) : G ⧸ p.ker.map ι) = ((ι b : G) : G ⧸ p.ker.map ι) ↔ p a = p b := by
  rw [QuotientGroup.eq]
  constructor
  · rintro ⟨k, hk, hke⟩
    have hk0 : p k = 1 := hk
    have hkb : k = a⁻¹ * b := hι (by rw [hke, map_mul, map_inv])
    rw [hkb, map_mul, map_inv, inv_mul_eq_one] at hk0
    exact hk0
  · intro h
    refine ⟨a⁻¹ * b, ?_, by rw [map_mul, map_inv]⟩
    show p (a⁻¹ * b) = 1
    rw [map_mul, map_inv, h, inv_mul_cancel]

private theorem exists_quotient_out_eq_and_eq_of_map_ker (ι : H →* G) (p : H →* Γ) (y : H) :
    ∃ z, Quotient.out ((ι y : G) : G ⧸ p.ker.map ι) = ι z ∧ p z = p y := by
  obtain ⟨⟨u, k, hk, rfl⟩, hu⟩ := QuotientGroup.mk_out_eq_mul (p.ker.map ι) (ι y)
  have hk0 : p k = 1 := hk
  exact ⟨y * k, by simp [hu], by rw [map_mul, hk0, mul_one]⟩

private theorem lev_eq [Fintype Γ] (ρ : Representation ℂ G V) (ι : H →* G) (hι : Function.Injective ι)
    (p : H →* Γ) (hp : Function.Surjective p) (f : G → ℂ) (fb : Γ → ℂ) (hf1 : ∀ y, f (ι y) = fb (p y))
    (hf0 : ∀ x, x ∉ ι.range → f x = 0) (A : V →ₗ[ℂ] V) {x : V} (hx : A x ∈ fixed ρ (p.ker.map ι)) :
    GlobalTheory.BCT.levOp ρ ι.range (p.ker.map ι) f A x =
      (Nat.card Γ : ℂ)⁻¹ • ∑ g : Γ, fb g • ρ (ι (Function.surjInv hp g)) (A x) := by
  classical
  let φ : Γ → G ⧸ p.ker.map ι := fun g => ((ι (Function.surjInv hp g) : G) : G ⧸ p.ker.map ι)
  have hφ : Function.Injective φ := by
    intro g g' h
    have h2 := (lev_eq_lemma ι hι p _ _).1 h
    rwa [Function.surjInv_eq hp, Function.surjInv_eq hp] at h2
  have hsupp : Function.support (fun q : G ⧸ p.ker.map ι => f (Quotient.out q) • ρ (Quotient.out q) ∘ₗ A) ⊆
      (Finset.univ.image φ : Set (G ⧸ p.ker.map ι)) := by
    intro q hq
    by_contra hn
    apply hq
    have hf : f (Quotient.out q) = 0 := by
      apply hf0
      intro hr
      obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 hr
      apply hn
      refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨p y, Finset.mem_univ _, ?_⟩)
      rw [← QuotientGroup.out_eq' q, ← hy]
      exact (lev_eq_lemma ι hι p _ _).2 (Function.surjInv_eq hp _)
    simp [hf]
  have hterm : ∀ g, f (Quotient.out (φ g)) • ρ (Quotient.out (φ g)) (A x) =
      fb g • ρ (ι (Function.surjInv hp g)) (A x) := by
    intro g
    obtain ⟨z, hz, hpz⟩ := exists_quotient_out_eq_and_eq_of_map_ker ι p (Function.surjInv hp g)
    show f (Quotient.out ((ι (Function.surjInv hp g) : G) : G ⧸ p.ker.map ι)) •
      ρ (Quotient.out ((ι (Function.surjInv hp g) : G) : G ⧸ p.ker.map ι)) (A x) = _
    rw [hz, hf1, hpz, Function.surjInv_eq hp]
    congr 1
    exact fx_eq ρ ι p hpz hx
  unfold GlobalTheory.BCT.levOp
  rw [rel_eq ι hι p hp, LinearMap.smul_apply, finsum_eq_sum_of_support_subset _ hsupp, LinearMap.sum_apply,
    Finset.sum_image (fun a _ b _ h => hφ h)]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [LinearMap.smul_apply, LinearMap.comp_apply]
  exact hterm g

private theorem tr_eq [Finite Γ] (ρ : Representation ℂ G V) (ι : H →* G) (hι : Function.Injective ι)
    (p : H →* Γ) (hp : Function.Surjective p) (f : G → ℂ) (fb : Γ → ℂ) (hf1 : ∀ y, f (ι y) = fb (p y))
    (hf0 : ∀ x, x ∉ ι.range → f x = 0) (A : V →ₗ[ℂ] V)
    (hA : ∀ x ∈ fixed ρ (p.ker.map ι), A x ∈ fixed ρ (p.ker.map ι)) :
    GlobalTheory.BCT.twTr ρ ι.range (p.ker.map ι) f A =
      (Nat.card Γ : ℂ)⁻¹ * LinearMap.trace ℂ _ (∑ᶠ g, fb g • (rp ρ ι p hp g ∘ₗ A.restrict hA)) := by
  haveI := Fintype.ofFinite Γ
  have hL : ∀ v ∈ fixed ρ (p.ker.map ι),
      GlobalTheory.BCT.levOp ρ ι.range (p.ker.map ι) f A v ∈ fixed ρ (p.ker.map ι) := by
    intro v hv
    rw [lev_eq ρ ι hι p hp f fb hf1 hf0 A (hA v hv)]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ ?_)
    exact fx_stable ρ ι p _ (hA v hv)
  unfold GlobalTheory.BCT.twTr
  rw [dite_eq_left hL, finsum_eq_sum_of_fintype, ← smul_eq_mul, ← map_smul]
  congr 1
  ext ⟨v, hv⟩
  simp only [LinearMap.restrict_apply, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    Submodule.coe_smul, Submodule.coe_sum]
  rw [lev_eq ρ ι hι p hp f fb hf1 hf0 A (hA v hv)]
  rfl

end Gen

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {F₀ : Type} [Field F₀]

private theorem iota_inj (n : ℕ) :
    Function.Injective (GeneralLinearGroup.map (n := Fin n) (algebraMap 𝒪[k] k)) := by
  intro a b h
  ext i j
  have h2 := congrArg (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) i j) h
  simpa using h2

private theorem unit_of_ne (rd : 𝒪[k] →+* F₀) (hrd : Function.Surjective rd) {x : 𝒪[k]} (hx : rd x ≠ 0) :
    IsUnit x := by
  by_contra hu
  apply hx
  have hmax := RingHom.ker_isMaximal_of_surjective rd hrd
  have hm : x ∈ IsLocalRing.maximalIdeal 𝒪[k] := (IsLocalRing.mem_maximalIdeal x).2 hu
  rw [← IsLocalRing.eq_maximalIdeal hmax] at hm
  exact (RingHom.mem_ker).1 hm

private theorem gl_onto (rd : 𝒪[k] →+* F₀) (hrd : Function.Surjective rd) (n : ℕ) :
    Function.Surjective (GeneralLinearGroup.map (n := Fin n) rd) := by
  intro g
  let M : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => Function.surjInv hrd ((g : Matrix (Fin n) (Fin n) F₀) i j)
  have hM : M.map rd = (g : Matrix (Fin n) (Fin n) F₀) := by
    ext i j
    rw [Matrix.map_apply]
    exact Function.surjInv_eq hrd _
  have hdet : IsUnit M.det := by
    apply unit_of_ne rd hrd
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hM]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
  refine ⟨Matrix.nonsingInvUnit M hdet, ?_⟩
  ext i j
  show rd (M i j) = _
  exact Function.surjInv_eq hrd _

private theorem infl_on (rd : 𝒪[k] →+* F₀) {n : ℕ} (fb : GL (Fin n) F₀ → ℂ) (y : GL (Fin n) 𝒪[k]) :
    infl rd fb (GeneralLinearGroup.map (algebraMap 𝒪[k] k) y) = fb (GeneralLinearGroup.map rd y) := by
  have h : ∃ y', GeneralLinearGroup.map (algebraMap 𝒪[k] k) y' = GeneralLinearGroup.map (algebraMap 𝒪[k] k) y :=
    ⟨y, rfl⟩
  unfold infl
  rw [dite_eq_left h, iota_inj (k := k) n h.choose_spec]

private theorem infl_off (rd : 𝒪[k] →+* F₀) {n : ℕ} (fb : GL (Fin n) F₀ → ℂ) (x : GL (Fin n) k)
    (hx : x ∉ (GeneralLinearGroup.map (n := Fin n) (algebraMap 𝒪[k] k)).range) : infl rd fb x = 0 := by
  unfold infl
  rw [dite_eq_right (fun h => hx (MonoidHom.mem_range.2 h))]

end Loc

end UpperTheory.Gal.InertialTypesAlt.L.FiniteActions

open UpperTheory.Gal.InertialTypesAlt.L.FiniteActions in
theorem UpperTheory.Gal.InertialTypesAlt.L.finAct :
    UpperTheory.Gal.InertialTypesAlt.L.FinAct := by
  intro k _ _ _ _ F₀ _ _ rd hrd n V _ _ ρ
  have hp := gl_onto rd hrd n
  refine ⟨fun g => hp g, rp ρ _ _ hp, fun y x => rp_spec ρ _ _ hp y x, fun fb A hA => ?_⟩
  exact tr_eq ρ _ (iota_inj n) _ hp (infl rd fb) fb (infl_on rd fb) (infl_off rd fb) A hA
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.SmallRad
open ValuativeRel Matrix Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc UpperTheory.Gal.Join
open GlobalTheory.SmGL hiding iwahori

namespace UpperTheory.Gal.InertialTypesAlt.L

section SlopeTestRemainingChoices

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem exists_rad {γ : ValueGroupWithZero k} (hγ : γ ≠ 0) :
    ∃ r : ValueGroupWithZero k, 0 < r ∧ r < 1 ∧ r < γ := by
  obtain ⟨x, hx0, hx1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
  have hc0 : 0 < valuation k x := zero_lt_iff.2 ((valuation k).ne_zero_iff.2 hx0)
  have hm0 : 0 < min γ 1 := lt_min (zero_lt_iff.2 hγ) zero_lt_one
  have hlt : valuation k x * min γ 1 < min γ 1 := mul_lt_of_lt_one_left hm0 hx1
  exact ⟨valuation k x * min γ 1, mul_pos hc0 hm0, hlt.trans_le (min_le_right _ _), hlt.trans_le (min_le_left _ _)⟩

private theorem nhds_rad {x : k} {W : Set k} (hW : W ∈ 𝓝 x) :
    ∃ r : ValueGroupWithZero k, 0 < r ∧ r < 1 ∧ {y | valuation k (y - x) ≤ r} ⊆ W := by
  obtain ⟨γ, hγ, hs⟩ := (IsValuativeTopology.hasBasis_nhds' x).mem_iff.1 hW
  obtain ⟨r, h0, h1, h2⟩ := exists_rad hγ
  exact ⟨r, h0, h1, fun y hy => hs (lt_of_le_of_lt hy h2)⟩

private theorem fin_rad {ι : Type} [Finite ι] (R : ι → ValueGroupWithZero k) (h0 : ∀ i, 0 < R i) (h1 : ∀ i, R i < 1) :
    ∃ r : ValueGroupWithZero k, 0 < r ∧ r < 1 ∧ ∀ i, r ≤ R i := by
  obtain ⟨c, hc0, hc1, -⟩ := exists_rad (k := k) one_ne_zero
  obtain ⟨o, ho⟩ := Finite.exists_min (fun o : Option ι => o.elim c R)
  refine ⟨o.elim c R, ?_, ?_, fun i => ho (some i)⟩
  · cases o with
    | none => exact hc0
    | some i => exact h0 i
  · cases o with
    | none => exact hc1
    | some i => exact h1 i

private theorem pi_rad {ι : Type} [Finite ι] {X : ι → Type} [∀ i, TopologicalSpace (X i)] (x : ∀ i, X i)
    (P : ∀ i, ValueGroupWithZero k → Set (X i))
    (hP : ∀ i, ∀ W ∈ 𝓝 (x i), ∃ r : ValueGroupWithZero k, 0 < r ∧ r < 1 ∧ P i r ⊆ W)
    (hm : ∀ i r r', r' ≤ r → P i r' ⊆ P i r) {V : Set (∀ i, X i)} (hV : V ∈ 𝓝 x) :
    ∃ r : ValueGroupWithZero k, 0 < r ∧ r < 1 ∧ {y | ∀ i, y i ∈ P i r} ⊆ V := by
  rw [nhds_pi, Filter.mem_pi'] at hV
  obtain ⟨I, t, ht, hsub⟩ := hV
  choose R h0 h1 hR using fun i => hP i (t i) (ht i)
  obtain ⟨r, hr0, hr1, hr⟩ := fin_rad R h0 h1
  exact ⟨r, hr0, hr1, fun y hy => hsub fun i _ => hR i (hm i _ _ (hr i) (hy i))⟩

private theorem mat_rad {n : ℕ} {V : Set (Matrix (Fin n) (Fin n) k)} (hV : V ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) k)) :
    ∃ r : ValueGroupWithZero k, 0 < r ∧ r < 1 ∧
      {M : Matrix (Fin n) (Fin n) k | ∀ i j, valuation k (M i j - (1 : Matrix (Fin n) (Fin n) k) i j) ≤ r} ⊆ V := by
  refine pi_rad (X := fun _ : Fin n => Fin n → k) (fun i j => (1 : Matrix (Fin n) (Fin n) k) i j)
    (fun i r => {y | ∀ j, valuation k (y j - (1 : Matrix (Fin n) (Fin n) k) i j) ≤ r}) (fun i W hW => ?_)
    (fun i r r' h y hy j => (hy j).trans h) hV
  exact pi_rad (X := fun _ : Fin n => k) (fun j => (1 : Matrix (Fin n) (Fin n) k) i j)
    (fun j r => {y | valuation k (y - (1 : Matrix (Fin n) (Fin n) k) i j) ≤ r}) (fun j W hW => nhds_rad hW)
    (fun j r r' h y hy => (show valuation k (y - (1 : Matrix (Fin n) (Fin n) k) i j) ≤ r from le_trans hy h)) hW

private theorem unit_nhds {A : Type} [Monoid A] [TopologicalSpace A] {U : Set Aˣ} (hU : U ∈ 𝓝 (1 : Aˣ)) :
    ∃ V ∈ 𝓝 (1 : A), ∀ g : Aˣ, (g : A) ∈ V → ((g⁻¹ : Aˣ) : A) ∈ V → g ∈ U := by
  rw [Units.isEmbedding_embedProduct.isInducing.nhds_eq_comap, Filter.mem_comap] at hU
  obtain ⟨T, hT, hTU⟩ := hU
  obtain ⟨a, ha, b, hb, hab⟩ := mem_nhds_prod_iff.1 (by simpa using hT)
  refine ⟨a ∩ MulOpposite.op ⁻¹' b, Filter.inter_mem ha
    (MulOpposite.continuous_op.continuousAt.preimage_mem_nhds (by simpa using hb)), fun g h1 h2 => hTU ?_⟩
  exact hab ⟨h1.1, h2.2⟩

private theorem val_near {r : ValueGroupWithZero k} (h1 : r < 1) {x : k} (hx : valuation k (x - 1) ≤ r) :
    valuation k x = 1 := by
  have h := Valuation.map_one_add_of_lt (valuation k) (lt_of_le_of_lt hx h1)
  simpa using h

private theorem near_mul' {r : ValueGroupWithZero k} (h1 : r < 1) {x y : k} (hx : valuation k (x - 1) ≤ r)
    (hy : valuation k (y - 1) ≤ r) : valuation k (x * y - 1) ≤ r := by
  have e : x * y - 1 = x * (y - 1) + (x - 1) := by ring
  rw [e]
  refine Valuation.map_add_le _ ?_ hx
  rw [map_mul, val_near h1 hx, one_mul]
  exact hy

private theorem near_inv' {r : ValueGroupWithZero k} (h1 : r < 1) (x : kˣ) (hx : valuation k ((x : k) - 1) ≤ r) :
    valuation k (((x⁻¹ : kˣ) : k) - 1) ≤ r := by
  have hv := val_near h1 hx
  have e : ((x⁻¹ : kˣ) : k) - 1 = -((x : k) - 1) * ((x⁻¹ : kˣ) : k) := by
    rw [neg_mul, sub_mul, Units.mul_inv]
    ring
  have hv' : valuation k ((x⁻¹ : kˣ) : k) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hv, inv_one]
  rw [e, map_mul, hv', mul_one, Valuation.map_neg]
  exact hx

private theorem t2 : T2Space k := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  letI : (Valued.v (R := k)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  infer_instance

private theorem compact_units (r : ValueGroupWithZero k) (h1 : r < 1) :
    IsCompact {x : kˣ | valuation k ((x : k) - 1) ≤ r} := by
  haveI : T2Space k := t2
  have hC : IsCompact {x : k | valuation k (x - 1) ≤ r} := by
    have h := (IsNonarchimedeanLocalField.isCompact_closedBall k r).image (f := fun x => x + 1) (by fun_prop)
    convert h using 1
    ext x
    constructor
    · intro hx
      exact ⟨x - 1, hx, sub_add_cancel _ _⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  have h := (Units.isClosedEmbedding_embedProduct (α := k)).isCompact_preimage
    (hC.prod (hC.image MulOpposite.continuous_op))
  convert h using 1
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod,
    MulOpposite.op_injective.mem_set_image]
  exact ⟨fun hx => ⟨hx, near_inv' h1 x hx⟩, fun hx => hx.1⟩

end SlopeTestRemainingChoices

theorem smallRad :
    UpperTheory.Gal.InertialTypesAlt.L.SmallRad := by
  intro k _ _ _ _ n
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro U hU
    obtain ⟨V, hV, hVU⟩ := unit_nhds hU
    obtain ⟨r, h0, h1, hr⟩ := mat_rad hV
    obtain ⟨K, hK, -, -⟩ := UpperTheory.ConvolutionTheory.Loc.ballSub k n r h0 h1
    refine ⟨r, h0, h1, fun r' hr' g hg => ?_⟩
    have hg' : g ∈ ball n r := fun i j => (hg i j).trans hr'
    have hgK : g ∈ K := by
      have : g ∈ (K : Set (GL (Fin n) k)) := hK ▸ hg'
      exact this
    have hinv : g⁻¹ ∈ ball n r := by
      have : g⁻¹ ∈ (K : Set (GL (Fin n) k)) := K.inv_mem hgK
      exact hK ▸ this
    exact hVU g (hr hg') (hr hinv)
  · intro W hW
    obtain ⟨r, h0, h1, hr⟩ := pi_rad (X := fun _ : Fin n => kˣ) (1 : Fin n → kˣ)
      (fun _ r => {u : kˣ | valuation k ((u : k) - 1) ≤ r}) (fun i Y hY => by
        obtain ⟨V, hV, hVU⟩ := unit_nhds hY
        obtain ⟨r, h0, h1, hr⟩ := nhds_rad hV
        exact ⟨r, h0, h1, fun u hu => hVU u (hr hu) (hr (near_inv' h1 u hu))⟩)
      (fun _ r r' h y hy => (show valuation k ((y : k) - 1) ≤ r from le_trans hy h)) hW
    exact ⟨r, h0, h1, fun r' hr' u hu => hr fun i => (hu i).trans hr'⟩
  · intro r h1
    refine ⟨{ carrier := {u | Near r u}
              one_mem' := fun i => by simp
              mul_mem' := fun {a b} ha hb i => by
                simpa using near_mul' h1 (ha i) (hb i)
              inv_mem' := fun {a} ha i => by
                simpa using near_inv' h1 (a i) (ha i) }, fun u => Iff.rfl, ?_⟩
    have h := isCompact_univ_pi (fun _ : Fin n => compact_units r h1)
    convert h using 1
    ext u
    simp [Near, Set.mem_pi]
  · exact (continuous_leviEmb k (points (Fin n))).comp (continuous_leviTorus k (Fin n))
  · obtain ⟨x, hx0, hx1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation k)
    refine ⟨fun i => Units.mk0 x hx0 ^ (n - (i : ℕ)), fun i j hij => ?_⟩
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0, map_pow]
    have hij' : (i : ℕ) < j := hij
    exact pow_lt_pow_right_of_lt_one₀ (zero_lt_iff.2 ((valuation k).ne_zero_iff.2 hx0)) hx1 (by omega)
  · intro t₀ t h₀ ht i j hij
    have a := h₀ i j hij
    have b := ht i j hij
    have c : 0 < valuation k (t j : k) := zero_lt_iff.2 (by simp)
    simp only [Pi.mul_apply, Units.val_mul, map_mul]
    calc valuation k (t₀ i : k) * valuation k (t i : k) ≤ valuation k (t₀ i : k) * valuation k (t j : k) :=
          mul_le_mul_right b _
      _ < valuation k (t₀ j : k) * valuation k (t j : k) := mul_lt_mul_of_pos_right a c

end UpperTheory.Gal.InertialTypesAlt.L
end
