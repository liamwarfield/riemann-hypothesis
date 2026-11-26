module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.G1
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DeRhamInj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.HarmEx

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.ImportsVariant
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.IndepAbs
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.indepAbs :
    UpperTheory.V.Lit.Bor.IndepAbs := by
  classical
  intro O W _ _ A s V h hs hn
  have hsup : ∀ P Q : Submodule ℂ W, (∀ o, ∀ x ∈ P, A o x ∈ P) → (∀ o, ∀ x ∈ Q, A o x ∈ Q) →
      ∀ o, ∀ x ∈ P ⊔ Q, A o x ∈ P ⊔ Q := by
    intro P Q hP hQ o x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (hP o y hy) (hQ o z hz)
  have hfs : ∀ t : Finset (Fin s), ∀ o, ∀ x ∈ t.sup V, A o x ∈ t.sup V := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro o x hx
      simp only [Finset.sup_empty, Submodule.mem_bot] at hx ⊢
      rw [hx, map_zero]
    | insert j t hj ih =>
      rw [Finset.sup_insert]
      exact hsup _ _ (h j) ih
  have key : ∀ t : Finset (Fin s), ∀ i, i ∉ t → Disjoint (V i) (t.sup V) := by
    intro t
    induction t using Finset.induction_on with
    | empty => intro i _; simp
    | insert j t hj ih =>
      intro i hi
      rw [Finset.mem_insert, not_or] at hi
      obtain ⟨hij, hit⟩ := hi
      have hSinv := hfs t
      have hiS := ih i hit
      have hjS := ih j hj
      rw [Finset.sup_insert, disjoint_iff]
      set S := t.sup V with hSdef
      by_cases hVi : V i = ⊥
      · rw [hVi, bot_inf_eq]
      have hM : ∀ o, ∀ x ∈ V i ⊓ (V j ⊔ S), A o x ∈ V i ⊓ (V j ⊔ S) :=
        fun o x hx => ⟨h i o x hx.1, hsup _ _ (h j) hSinv o x hx.2⟩
      rcases hs i _ inf_le_left hM with hbot | htop
      · exact hbot
      exfalso
      have hle : V i ≤ V j ⊔ S := inf_eq_left.mp htop
      have huniq : ∀ y y' : V j, ((y : W) - y') ∈ S → y = y' := by
        intro y y' hyy
        have h0 : ((y : W) - y') ∈ V j ⊓ S := ⟨sub_mem y.2 y'.2, hyy⟩
        rw [disjoint_iff.mp hjS, Submodule.mem_bot, sub_eq_zero] at h0
        exact Subtype.ext h0
      let fj : V j →ₗ[ℂ] W ⧸ S := S.mkQ ∘ₗ (V j).subtype
      have hfj : Function.Injective fj := by
        intro a b hab
        exact huniq a b ((Submodule.Quotient.eq S).mp hab)
      let ej := LinearEquiv.ofInjective fj hfj
      let fi : V i →ₗ[ℂ] W ⧸ S := S.mkQ ∘ₗ (V i).subtype
      have hrange : ∀ x : V i, fi x ∈ LinearMap.range fj := by
        intro x
        obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (hle x.2)
        refine ⟨⟨y, hy⟩, ?_⟩
        show S.mkQ y = S.mkQ x
        rw [← hyz, map_add (f := _), Submodule.mkQ_apply S z, (Submodule.Quotient.mk_eq_zero S).mpr hz,
          add_zero]
      let T : V i →ₗ[ℂ] V j := ej.symm.toLinearMap ∘ₗ (fi.codRestrict (LinearMap.range fj) hrange)
      have hT : ∀ x : V i, ((T x : W) - x) ∈ S := by
        intro x
        have e0 : T x = ej.symm ⟨fi x, hrange x⟩ := rfl
        have e1 := ej.apply_symm_apply ⟨fi x, hrange x⟩
        rw [Subtype.ext_iff, LinearEquiv.ofInjective_apply, ← e0] at e1
        exact (Submodule.Quotient.eq S).mp e1
      have hTeq : ∀ o (x : V i), T ((A o).restrict (h i o) x) = (A o).restrict (h j o) (T x) := by
        intro o x
        apply huniq
        have e1 := hT ((A o).restrict (h i o) x)
        have e2 : A o ((T x : W) - x) ∈ S := hSinv o _ (hT x)
        have e3 : ((T ((A o).restrict (h i o) x) : W) - ((A o).restrict (h j o) (T x) : W))
            = ((T ((A o).restrict (h i o) x) : W) - ((A o).restrict (h i o) x : W))
              - A o ((T x : W) - x) := by
          simp only [LinearMap.restrict_coe_apply, map_sub]
          abel
        rw [e3]
        exact sub_mem e1 e2
      have hTinj : Function.Injective T := by
        rw [← LinearMap.ker_eq_bot, eq_bot_iff]
        intro x hx
        rw [LinearMap.mem_ker] at hx
        have e1 := hT x
        rw [hx, Submodule.coe_zero, zero_sub] at e1
        have hxS : (x : W) ∈ S := by simpa using S.neg_mem e1
        have e2 : (x : W) ∈ V i ⊓ S := ⟨x.2, hxS⟩
        rw [disjoint_iff.mp hiS, Submodule.mem_bot] at e2
        exact (Submodule.mem_bot ℂ).mpr (Subtype.ext e2)
      let N := (LinearMap.range T).map (V j).subtype
      have hNle : N ≤ V j := Submodule.map_subtype_le _ _
      have hNinv : ∀ o, ∀ x ∈ N, A o x ∈ N := by
        intro o x hx
        obtain ⟨y, ⟨z, rfl⟩, rfl⟩ := hx
        refine ⟨T ((A o).restrict (h i o) z), ⟨_, rfl⟩, ?_⟩
        rw [hTeq]
        rfl
      have hTsurj : Function.Surjective T := by
        rcases hs j N hNle hNinv with hN0 | hNj
        · exfalso
          obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVi
          have hmem : ((T ⟨x, hx⟩ : V j) : W) ∈ N := ⟨T ⟨x, hx⟩, ⟨_, rfl⟩, rfl⟩
          rw [hN0, Submodule.mem_bot] at hmem
          have : T ⟨x, hx⟩ = T 0 := by rw [map_zero]; exact Subtype.ext hmem
          exact hx0 (congrArg Subtype.val (hTinj this))
        · intro y
          have hy : (y : W) ∈ N := by rw [hNj]; exact y.2
          obtain ⟨y', ⟨z, rfl⟩, hz⟩ := hy
          exact ⟨z, Subtype.ext hz⟩
      exact hn i j hij ⟨LinearEquiv.ofBijective T ⟨hTinj, hTsurj⟩, hTeq⟩
  rw [iSupIndep_iff_supIndep]
  intro t u _ i _ hiu
  exact key u i hiu
end

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.indep :
    UpperTheory.V.Lit.Bor.Indep := by
  intro E _ _ _ a d q s π hπ ω h0 hV c hc
  have hind : iSupIndep fun i => (π i).V :=
    UpperTheory.V.Lit.Bor.indepAbs _ (Sm E a) (fun o => act o) s (fun i => (π i).V) (fun i o x hx => (π i).stable o x hx)
      (fun i N hN hst => (π i).irred N hN hst) (fun i j hij h => hij (hπ i j h))
  have key : ∀ (X : Fin q → Herm E a) (k : Fin d) (i : Fin s), c i • cmp k (ω i X) = 0 := by
    intro X k i
    have h : ∀ (t : Finset (Fin s)) (f : Fin s → Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin d → ℂ))),
        (∑ j ∈ t, f j) X = ∑ j ∈ t, f j X := fun t f => by
      induction t using Finset.cons_induction with
      | empty => rfl
      | cons j t hj ih => rw [Finset.sum_cons, Finset.sum_cons, add_apply, ih]
    have h1 : ∑ j, c j • cmp k (ω j X) = 0 := by
      have h2 := congrArg (fun η => cmp k (η X)) hc
      set_option synthInstance.maxHeartbeats 100000 in
        simpa only [h, map_sum, smul_apply, map_smul, zero_apply, map_zero] using h2
    exact (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).1 hind Finset.univ (fun j => c j • cmp k (ω j X))
      (fun j _ => Submodule.smul_mem _ _ (mem_tens.1 (hV j X) k)) h1 i (Finset.mem_univ i)
  funext i
  by_contra hci
  refine h0 i (AlternatingMap.ext fun X => ?_)
  rw [← sum_cmp (ω i X), zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [(smul_eq_zero.1 (key X k i)).resolve_left hci, TensorProduct.zero_tmul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Imports
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.count :
    UpperTheory.V.Lit.Bor.Count := by
  classical
  intro X S deg κ hκ
  have hq : ∀ q, Cardinal.mk {x : S // deg x = q} ≤ κ q := by
    intro q
    let e := Fintype.equivFin {x : S // deg x = q}
    rw [Cardinal.mk_fintype]
    refine hκ q _ (fun i => ((e.symm i).1 : X)) ?_ (fun i => ⟨(e.symm i).1.2, (e.symm i).2⟩)
    intro i j hij
    exact e.symm.injective (Subtype.ext (Subtype.ext hij))
  calc (S.card : Cardinal) = Cardinal.mk S := (Cardinal.mk_coe_finset).symm
    _ = Cardinal.mk (Σ q, {x : S // deg x = q}) :=
        (Cardinal.mk_congr (Equiv.sigmaFiberEquiv (fun x : S => deg x))).symm
    _ = Cardinal.sum (fun q => Cardinal.mk {x : S // deg x = q}) := Cardinal.mk_sigma _
    _ ≤ Cardinal.sum κ := Cardinal.sum_le_sum _ _ hq
end

open UpperTheory.V.Lit.Geo

section
open NumberField Matrix MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC
open UpperTheory.V.Lit UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} {Ξ : AlgRep E a}

private theorem rapid_of_rapidD {q : ℕ} {ω : Co Ξ q} (h : RapidD ω) : Rapid ω := fun X N => h [] X N

private theorem ev_add' (x y : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) (g : GA E a) : ev (x + y) g = ev x g + ev y g := by
  ext i; simp [ev]

private theorem ev_smul' (c : ℂ) (x : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) (g : GA E a) : ev (c • x) g = c • ev x g := by
  ext i; simp [ev]

private theorem rapid_sum {q s : ℕ} (ω : Fin s → Co Ξ q) (c : Fin s → ℂ) (h : ∀ i, Rapid (ω i)) :
    Rapid (∑ i, c i • ω i) := by
  have hq : ∀ g : GA E a, 0 ≤ qht g := fun g => zero_le_one.trans ((qhtFacts E a).1 g)
  refine Finset.sum_induction _ (fun ω : Co Ξ q => Rapid ω) ?_ ?_ ?_
  · intro α β hα hβ X N
    obtain ⟨C, hC⟩ := hα X N
    obtain ⟨D, hD⟩ := hβ X N
    refine ⟨C + D, fun g => ?_⟩
    rw [AlternatingMap.add_apply, ev_add']
    refine (mul_le_mul_of_nonneg_right (norm_add_le _ _) (pow_nonneg (hq _) N)).trans ?_
    rw [add_mul]
    exact add_le_add (hC g) (hD g)
  · intro X N
    refine ⟨0, fun g => ?_⟩
    have : ev ((0 : Co Ξ q) X) g.1 = 0 := by
      have := ev_smul' (Ξ := Ξ) 0 0 g.1
      simpa using this
    rw [this]; simp
  · intro i _ X N
    obtain ⟨C, hC⟩ := h i X N
    refine ⟨‖c i‖ * C, fun g => ?_⟩
    rw [AlternatingMap.smul_apply, ev_smul', norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC g) (norm_nonneg _)

private theorem noExact' (ha : 1 ≤ a) {n : ℕ} {e : Fin n → Herm E a} (he : IsFrame e) {U : Subgroup (GL (Fin a) (Af E))}
    (hUo : IsOpen (U : Set (GL (Fin a) (Af E)))) (hUc : IsCompact (U : Set (GL (Fin a) (Af E)))) {r : ℝ} (hr : HasOne Ξ r)
    {q : ℕ} (ω : Co Ξ q) (hω : IsHarm U Ξ r e ω) (hR : Rapid ω) (hex : IsRelExact U Ξ ω) : ω = 0 := by
  cases q with
  | zero => exact hex
  | succ q =>
    obtain ⟨η, hη, rfl⟩ := hex
    obtain ⟨χ, hχ⟩ := twEx E a ha r
    obtain ⟨G, hG⟩ := admEx E a Ξ
    have hd : IsData Ξ r χ G e := ⟨hr, hχ, hG, he⟩
    have hL : IsLev U Ξ (dCo (smLie Ξ) η) := ((harmLin E a n e U Ξ r (q + 1)).2 _).1 hω
    have hM : Moderate (dCo (smLie Ξ) η) := ⟨0, fun X => by
      obtain ⟨C, hC⟩ := hR X 0
      exact ⟨C, fun g => by simpa using hC g⟩⟩
    have hP := pairFacts E a ha Measure.haar U hUo Ξ r χ G n e hd (q + 1)
    exact hP.2.2.1 _ hL (hP.1 _ _ hL hL hR hM)
      (g1 E a ha Measure.haar U hUo hUc Ξ r χ G n e hd q _ η hL hη hR hω.coclosed hM)

theorem UpperTheory.V.Lit.Geo.borelInjC :
    UpperTheory.V.Published.BorelInjC := by
  intro E _ _ _ a ha U hUo hUc Ξ S hS hC
  classical
  obtain ⟨n, e, he⟩ := frameEx E a
  obtain ⟨r, hr⟩ := oneReal E a Ξ
  have hex : ∀ π : CuspSub E a, ∃ (q : ℕ) (ω : Co Ξ q),
      π ∈ S → ω ≠ 0 ∧ IsHarm U Ξ r e ω ∧ ∀ X, ω X ∈ tens Ξ.d π.V := fun π => by
    by_cases h : π ∈ S
    · obtain ⟨q, ω, hω⟩ := harmEx E a ha n e he U hUc π Ξ r hr (hC π h).1 (hC π h).2
      exact ⟨q, ω, fun _ => hω⟩
    · exact ⟨0, 0, fun h' => absurd h' h⟩
  choose deg w hw using hex
  refine UpperTheory.V.Lit.Bor.count _ S deg _ fun q s f hf hq => ?_
  have hex2 : ∀ i, ∃ ω : Co Ξ q, ω ≠ 0 ∧ IsHarm U Ξ r e ω ∧ ∀ X, ω X ∈ tens Ξ.d (f i).V := fun i => by
    obtain ⟨hi, rfl⟩ := hq i
    exact ⟨w _, hw _ hi⟩
  choose ω h0 hH hV using hex2
  refine deRhamInj E a ha U hUo hUc Ξ q s ω
    (fun i => ⟨((harmLin E a n e U Ξ r q).2 _).1 (hH i), (hH i).closed⟩) fun c hc => ?_
  exact indep E a Ξ.d q s f (fun i j h => hf (hS _ (hq i).1 _ (hq j).1 h)) ω h0 hV c
    (noExact' ha he hUo hUc hr _ ((harmLin E a n e U Ξ r q).1 s ω c hH)
      (rapid_sum ω c fun i => rapid_of_rapidD (cuspRapid E a (f i) Ξ q (ω i) (hV i))) hc)

end
