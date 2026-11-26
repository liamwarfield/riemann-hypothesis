module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinateFormSymmetricNondegenerate
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictedProductIntegral

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SlotLevelSubgroupsExistStatement
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorLevelSubgroupsExist
open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical
open GlobalTheory.CompanionTheory.FinActS

noncomputable section

namespace GlobalTheory.CompanionTheory.PositionTest

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem eventually_factor {S : Set (Pl E)} {P : Slot S → Prop}
    (h₁ : ∀ᶠ w : Pl E in cofinite, ∀ hw : w ∈ S, P (Sum.inl ⟨w, hw⟩))
    (h₂ : ∀ᶠ w : Pl E in cofinite, ∀ hw : w ∈ S ∧ IsSplitAt w, P (Sum.inr ⟨w, hw⟩)) :
    ∀ᶠ i : Slot S in cofinite, P i := by
  have f₁ := Filter.eventually_cofinite.1 h₁
  have f₂ := Filter.eventually_cofinite.1 h₂
  refine Filter.eventually_cofinite.2 ?_
  refine (((f₁.preimage (Subtype.val_injective (p := fun w => w ∈ S)).injOn).image Sum.inl).union
    ((f₂.preimage (Subtype.val_injective (p := fun w => w ∈ S ∧ IsSplitAt w)).injOn).image Sum.inr)).subset ?_
  rintro (⟨w, hw⟩ | ⟨w, hw⟩) hi
  · exact Or.inl ⟨⟨w, hw⟩, fun h => hi (h hw), rfl⟩
  · exact Or.inr ⟨⟨w, hw⟩, fun h => hi (h hw), rfl⟩

def localLevel {S : Set (Pl E)} (L₁ L₂ : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)) :
    ∀ i : Slot S, Subgroup (GLw a i.pl × GLw b i.pl)
  | .inl w => L₁ w.1
  | .inr w => L₂ w.1

theorem exists_factor_level₂ {S : Set (Pl E)} {φ₁ φ₂ : ∀ w : Pl E, LF a b w} (h₁ : IsTestP φ₁) (h₂ : IsTestP φ₂) :
    ∃ L : ∀ i : Slot S, Subgroup (GLw a i.pl × GLw b i.pl),
      (∀ i, IsOpen (L i : Set (GLw a i.pl × GLw b i.pl))) ∧ (∀ᶠ i in cofinite, L i = K2 a b i.pl) ∧
      (∀ i, ∀ k ∈ L i, ∀ x, sf φ₁ φ₂ i (x * k) = sf φ₁ φ₂ i x) ∧
      (∀ i : Slot S, HasCompactSupport (sf φ₁ φ₂ i)) ∧
      ∀ᶠ i : Slot S in cofinite, sf φ₁ φ₂ i = (K2 a b i.pl : Set (GLw a i.pl × GLw b i.pl)).indicator 1 := by
  obtain ⟨L₁, o₁, e₁, i₁⟩ := GlobalTheory.CompanionTheory.FinLevelTw.exists_level_of_test h₁
  obtain ⟨L₂, o₂, e₂, i₂⟩ := GlobalTheory.CompanionTheory.FinLevelTw.exists_level_of_test h₂
  have c₁ := GlobalTheory.CompanionTheory.FinTestTw.eventually_eq_indicator h₁
  have c₂ := GlobalTheory.CompanionTheory.FinTestTw.eventually_eq_indicator h₂
  refine ⟨localLevel L₁ L₂, ?_, ?_, ?_, ?_, ?_⟩
  · rintro (w | w)
    · exact o₁ w.1
    · exact o₂ w.1
  · exact eventually_factor (e₁.mono fun w h _ => h) (e₂.mono fun w h _ => h)
  · rintro (w | w) k hk x
    · exact (i₁ w.1 k hk x).2
    · exact (i₂ w.1 k hk x).2
  · rintro (w | w)
    · exact GlobalTheory.CompanionTheory.FinTestTw.hasCompactSupport_loc h₁ w.1
    · exact GlobalTheory.CompanionTheory.FinTestTw.hasCompactSupport_loc h₂ w.1
  · exact eventually_factor (c₁.mono fun w h _ => h) (c₂.mono fun w h _ => h)

end GlobalTheory.CompanionTheory.PositionTest

end
end

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical
open GlobalTheory.CompanionTheory.FinActS

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.position_level_subgroups_exist : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {S : Set (Pl E)} {φ₁ φ₂ : ∀ w : Pl E, LF a b w} (h₁ : IsTestP φ₁) (h₂ : IsTestP φ₂),
    ∃ L : ∀ i : Slot S, Subgroup (GLw a i.pl × GLw b i.pl),
      (∀ i, IsOpen (L i : Set (GLw a i.pl × GLw b i.pl))) ∧ (∀ᶠ i in cofinite, L i = K2 a b i.pl) ∧
      (∀ i, ∀ k ∈ L i, ∀ x, sf φ₁ φ₂ i (x * k) = sf φ₁ φ₂ i x) ∧
      (∀ i : Slot S, HasCompactSupport (sf φ₁ φ₂ i)) ∧
      ∀ᶠ i : Slot S in cofinite, sf φ₁ φ₂ i = (K2 a b i.pl : Set (GLw a i.pl × GLw b i.pl)).indicator 1 := by
  first | exact @GlobalTheory.CompanionTheory.PositionTest.exists_factor_level₂ | exact GlobalTheory.CompanionTheory.PositionTest.exists_factor_level₂ | (intros; apply GlobalTheory.CompanionTheory.PositionTest.exists_factor_level₂ <;> assumption)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictedProductEmbeddings
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictedProductEmbeddings
open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical
open GlobalTheory.CompanionTheory.FinActS

namespace GlobalTheory.CompanionTheory.FinActS

theorem map_list_prod_embed_of_nodup {ι Γ : Type} [Group Γ] {Hl : ι → Type} [∀ i, Group (Hl i)]
    (p : ∀ i, Γ →* Hl i) (e : ∀ i, Hl i →* Γ)
    (hpe : ∀ i m, p i (e i m) = m) (hpe' : ∀ i j m, i ≠ j → p j (e i m) = 1)
    (f : ∀ i, Hl i) (j : ι) (l : List ι) (hl : l.Nodup) :
    p j (l.map fun i => e i (f i)).prod = if j ∈ l then f j else 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hnd := List.nodup_cons.mp hl
    have ih' := ih hnd.2
    rw [List.map_cons, List.prod_cons, map_mul, ih']
    by_cases hja : a = j
    · subst hja
      simp [hnd.1, hpe]
    · have hne : ¬ j = a := fun h => hja h.symm
      rw [hpe' a j _ hja, one_mul]
      simp [hne]

theorem exists_local_levels_le_open : ∀ {ι Γ : Type} [Group Γ] {Hl : ι → Type} [∀ i, Group (Hl i)] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [∀ i, TopologicalSpace (Hl i)] [∀ i, T2Space (Hl i)]
    (p : ∀ i, Γ →* Hl i) (e : ∀ i, Hl i →* Γ) (K : Subgroup Γ) (KH : ∀ i, Subgroup (Hl i))
    (hpc : ∀ i, Continuous (p i)) (hec : ∀ i, Continuous (e i))
    (hpe : ∀ i m, p i (e i m) = m) (hpe' : ∀ i j m, i ≠ j → p j (e i m) = 1)
    (hsep : ∀ x y : Γ, (∀ i, p i x = p i y) → x = y)
    (hK : ∀ x, x ∈ K ↔ ∀ i, p i x ∈ KH i) (hKc : IsCompact (K : Set Γ))
    (hKo : ∀ i, IsOpen (KH i : Set (Hl i))) (U : Subgroup Γ) (hU : IsOpen (U : Set Γ)),
    ∃ V : ∀ i, Subgroup (Hl i), (∀ i, IsOpen (V i : Set (Hl i))) ∧ (∀ i, V i ≤ KH i) ∧
      (∀ᶠ i in cofinite, V i = KH i) ∧ ∀ u, (∀ i, p i u ∈ V i) → u ∈ U := by
  intro ι Γ _ Hl _ _ _ _ _ p e K KH hpc hec hpe hpe' hsep hK hKc hKo U hU
  classical
  have hcomp : IsCompact ((K : Set Γ) \ (U : Set Γ)) := hKc.diff hU
  have hopen : ∀ i, IsOpen {x : Γ | p i x ≠ 1} := fun i =>
    (isOpen_ne (x := (1 : Hl i))).preimage (hpc i)
  have hcover : (K : Set Γ) \ (U : Set Γ) ⊆ ⋃ i, {x : Γ | p i x ≠ 1} := by
    intro x hx
    by_contra hcon
    have hall : ∀ i, p i x = p i 1 := by
      intro i
      by_contra hi
      exact hcon (Set.mem_iUnion.mpr ⟨i, by simpa using hi⟩)
    have hx1 : x = 1 := hsep x 1 hall
    exact hx.2 (hx1 ▸ U.one_mem)
  obtain ⟨T, hT⟩ := hcomp.elim_finite_subcover _ hopen hcover
  have hTU : ∀ x, x ∈ K → (∀ i ∈ T, p i x = 1) → x ∈ U := by
    intro x hxK hx
    by_contra hxU
    have hmem := hT ⟨hxK, hxU⟩
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hmem
    obtain ⟨i, hi, hne⟩ := hmem
    exact hne (hx i hi)
  refine ⟨fun i => if i ∈ T then KH i ⊓ U.comap (e i) else KH i, ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i ∈ T
    · simp only [hi, if_true]
      exact (hKo i).inter (hU.preimage (hec i))
    · simp only [hi, if_false]
      exact hKo i
  · intro i
    by_cases hi : i ∈ T
    · simp only [hi, if_true]
      exact inf_le_left
    · simp only [hi, if_false]
      exact le_rfl
  · have hfin : ∀ᶠ i in cofinite, i ∉ T := T.finite_toSet.compl_mem_cofinite
    filter_upwards [hfin] with i hi
    simp only [hi, if_false]
  · intro u hu
    have hle : ∀ i, p i u ∈ KH i := by
      intro i
      have := hu i
      by_cases hi : i ∈ T
      · simp only [hi, if_true] at this
        exact this.1
      · simpa only [hi, if_false] using this
    have huK : u ∈ K := (hK u).mpr hle
    set v : Γ := (T.toList.map fun i => e i (p i u)).prod with hv
    have hpv : ∀ j, p j v = if j ∈ T then p j u else 1 := by
      intro j
      have := map_list_prod_embed_of_nodup p e hpe hpe' (fun i => p i u) j T.toList T.nodup_toList
      simpa [hv] using this
    have hvU : v ∈ U := by
      refine U.list_prod_mem ?_
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have hiT : i ∈ T := Finset.mem_toList.mp hi
      have := hu i
      simp only [hiT, if_true] at this
      exact this.2
    have hwK : v⁻¹ * u ∈ K := by
      refine (hK _).mpr fun j => ?_
      rw [map_mul, map_inv, hpv j]
      by_cases hj : j ∈ T
      · simp [hj, (KH j).one_mem]
      · simpa [hj] using hle j
    have hwU : v⁻¹ * u ∈ U := by
      refine hTU _ hwK fun i hi => ?_
      rw [map_mul, map_inv, hpv i]
      simp [hi]
    have := U.mul_mem hvU hwU
    simpa using this

end GlobalTheory.CompanionTheory.FinActS
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictedProductEmbeddingsStatement
open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical
open GlobalTheory.CompanionTheory.FinActS

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restricted_product_embeddings : ∀ {ι Γ : Type} [Group Γ] {Hl : ι → Type} [∀ i, Group (Hl i)] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [∀ i, TopologicalSpace (Hl i)] [∀ i, T2Space (Hl i)]
    (p : ∀ i, Γ →* Hl i) (e : ∀ i, Hl i →* Γ) (K : Subgroup Γ) (KH : ∀ i, Subgroup (Hl i))
    (hpc : ∀ i, Continuous (p i)) (hec : ∀ i, Continuous (e i))
    (hpe : ∀ i m, p i (e i m) = m) (hpe' : ∀ i j m, i ≠ j → p j (e i m) = 1)
    (hsep : ∀ x y : Γ, (∀ i, p i x = p i y) → x = y)
    (hK : ∀ x, x ∈ K ↔ ∀ i, p i x ∈ KH i) (hKc : IsCompact (K : Set Γ))
    (hKo : ∀ i, IsOpen (KH i : Set (Hl i))) (U : Subgroup Γ) (hU : IsOpen (U : Set Γ)),
    ∃ V : ∀ i, Subgroup (Hl i), (∀ i, IsOpen (V i : Set (Hl i))) ∧ (∀ i, V i ≤ KH i) ∧
      (∀ᶠ i in cofinite, V i = KH i) ∧ ∀ u, (∀ i, p i u ∈ V i) → u ∈ U := by
  first | exact @GlobalTheory.CompanionTheory.FinActS.exists_local_levels_le_open | exact GlobalTheory.CompanionTheory.FinActS.exists_local_levels_le_open | (intros; apply GlobalTheory.CompanionTheory.FinActS.exists_local_levels_le_open <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTestFunctionProduct
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTestFunctionProduct
open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical
open GlobalTheory.CompanionTheory.FinActS

noncomputable section

namespace GlobalTheory.CompanionTheory.FinActS

theorem finprod_sum_split {α β M : Type*} [CommMonoid M] (f : α ⊕ β → M)
    (h₁ : (Function.mulSupport fun x => f (Sum.inl x)).Finite)
    (h₂ : (Function.mulSupport fun x => f (Sum.inr x)).Finite) :
    ∏ᶠ i, f i = (∏ᶠ x, f (Sum.inl x)) * ∏ᶠ x, f (Sum.inr x) := by
  have hu : (Set.univ : Set (α ⊕ β)) = Set.range Sum.inl ∪ Set.range Sum.inr := by
    ext i; cases i <;> simp
  have e₁ : (Set.range (Sum.inl : α → α ⊕ β) ∩ Function.mulSupport f).Finite := by
    refine (h₁.image Sum.inl).subset ?_
    rintro _ ⟨⟨x, rfl⟩, hx⟩
    exact ⟨x, hx, rfl⟩
  have e₂ : (Set.range (Sum.inr : β → α ⊕ β) ∩ Function.mulSupport f).Finite := by
    refine (h₂.image Sum.inr).subset ?_
    rintro _ ⟨⟨x, rfl⟩, hx⟩
    exact ⟨x, hx, rfl⟩
  have hd : Disjoint (Set.range (Sum.inl : α → α ⊕ β)) (Set.range (Sum.inr : β → α ⊕ β)) :=
    Set.disjoint_left.2 (by rintro _ ⟨x, rfl⟩ ⟨y, hy⟩; cases hy)
  rw [← finprod_mem_univ, hu, finprod_mem_union' hd e₁ e₂,
    finprod_mem_range Sum.inl_injective, finprod_mem_range Sum.inr_injective]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem finFn_eq_finprod_factor {S : Set (Pl E)} {φ₁ φ₂ : ∀ w : Pl E, LF a b w} (h₁ : IsTestP φ₁) (h₂ : IsTestP φ₂)
    (y : Hf E a b) : finFn S φ₁ φ₂ y = ∏ᶠ i : Slot S, sf φ₁ φ₂ i (i.cp a b y) := by
  set g₁ : Pl E → ℂ := fun w => φ₁ w (atW w y) with hg₁
  set g₂ : Pl E → ℂ := fun w => if IsSplitAt w then φ₂ w (atW w (thP E a b y)) else 1 with hg₂
  have o₁ : ∀ᶠ w in cofinite, g₁ w = 1 := by
    filter_upwards [GlobalTheory.CompanionTheory.FinTestTw.eventually_eq_indicator h₁, (GlobalTheory.CompanionTheory.FinTestTw.isRestrW a b).eventually_mem y] with w e m
    have m' : atW w y ∈ (K2 a b w : Set (GLw a w × GLw b w)) := m
    simp only [hg₁]
    rw [e, Set.indicator_of_mem m']
    simp
  have o₂ : ∀ᶠ w in cofinite, φ₂ w (atW w (thP E a b y)) = 1 := by
    filter_upwards [GlobalTheory.CompanionTheory.FinTestTw.eventually_eq_indicator h₂,
      (GlobalTheory.CompanionTheory.FinTestTw.isRestrW a b).eventually_mem (thP E a b y)] with w e m
    have m' : atW w (thP E a b y) ∈ (K2 a b w : Set (GLw a w × GLw b w)) := m
    rw [e, Set.indicator_of_mem m']
    simp
  have f₁ : (Function.mulSupport g₁).Finite := eventually_cofinite.1 o₁
  have f₂' : (Function.mulSupport fun w => φ₂ w (atW w (thP E a b y))).Finite := eventually_cofinite.1 o₂
  have f₂ : (Function.mulSupport g₂).Finite := by
    refine f₂'.subset fun w hw => ?_
    by_cases hs : IsSplitAt w
    · simpa [hg₂, hs, Function.mem_mulSupport] using hw
    · exact absurd (by simp [hg₂, hs]) hw
  have l₁ : (Function.mulSupport fun x : {w // w ∈ S} => g₁ x.1).Finite :=
    (f₁.preimage Subtype.val_injective.injOn).subset fun x hx => hx
  have l₂ : (Function.mulSupport fun x : {w // w ∈ S ∧ IsSplitAt w} => φ₂ x.1 (atW x.1 (thP E a b y))).Finite :=
    (f₂'.preimage Subtype.val_injective.injOn).subset fun x hx => hx
  have hs : ∏ᶠ i : Slot S, sf φ₁ φ₂ i (i.cp a b y) =
      (∏ᶠ x : {w // w ∈ S}, g₁ x.1) * ∏ᶠ x : {w // w ∈ S ∧ IsSplitAt w}, φ₂ x.1 (atW x.1 (thP E a b y)) :=
    finprod_sum_split (fun i : Slot S => sf φ₁ φ₂ i (i.cp a b y)) l₁ l₂
  have c₁ : ∏ᶠ x : {w // w ∈ S}, g₁ x.1 = ∏ᶠ w ∈ S, g₁ w :=
    finprod_subtype_eq_finprod_cond (f := g₁) (fun w => w ∈ S)
  have c₂ : ∏ᶠ x : {w // w ∈ S ∧ IsSplitAt w}, φ₂ x.1 (atW x.1 (thP E a b y)) = ∏ᶠ w ∈ S, g₂ w := by
    have e₀ : ∏ᶠ x : {w // w ∈ S ∧ IsSplitAt w}, φ₂ x.1 (atW x.1 (thP E a b y)) =
        ∏ᶠ x : {w // w ∈ S ∧ IsSplitAt w}, g₂ x.1 :=
      finprod_congr fun x => by simp [hg₂, x.2.2]
    rw [e₀, finprod_subtype_eq_finprod_cond (f := g₂) (fun w => w ∈ S ∧ IsSplitAt w)]
    refine finprod_mem_inter_mulSupport_eq' g₂ {w | w ∈ S ∧ IsSplitAt w} S fun w hw => ?_
    have hsp : IsSplitAt w := by
      by_contra hn
      exact hw (by simp [hg₂, hn])
    exact ⟨fun h => h.1, fun h => ⟨h, hsp⟩⟩
  rw [hs, c₁, c₂]
  exact finprod_mem_mul_distrib' (f₁.subset Set.inter_subset_right) (f₂.subset Set.inter_subset_right)

end GlobalTheory.CompanionTheory.FinActS

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTestFunctionProductStatement
open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical
open GlobalTheory.CompanionTheory.FinActS

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_test_function_product : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {S : Set (Pl E)} {φ₁ φ₂ : ∀ w : Pl E, LF a b w} (h₁ : IsTestP φ₁) (h₂ : IsTestP φ₂)
    (y : Hf E a b), finFn S φ₁ φ₂ y = ∏ᶠ i : Slot S, sf φ₁ φ₂ i (i.cp a b y) := by
  first | exact @GlobalTheory.CompanionTheory.FinActS.finFn_eq_finprod_factor | exact GlobalTheory.CompanionTheory.FinActS.finFn_eq_finprod_factor | (intros; apply GlobalTheory.CompanionTheory.FinActS.finFn_eq_finprod_factor <;> assumption)
end
end

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical

namespace GlobalTheory.CompanionTheory.FinActS

attribute [local instance] borelG borelF borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem relIndex_ne_zero_of_open {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] {V K : Subgroup H}
    (hV : IsOpen (V : Set H)) (hK : IsCompact (K : Set H)) : V.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI : Finite (K ⧸ V.subgroupOf K) :=
    Subgroup.quotient_finite_of_isOpen _ (hV.preimage continuous_subtype_val)
  exact Subgroup.index_ne_zero_of_finite

theorem finH_mul (x y : Hf E a b) : finH (x * y) = finH x * finH y :=
  Prod.ext (map_mul (finGL E a) _ _) (map_mul (finGL E b) _ _)

theorem finH_one : finH (1 : Hf E a b) = 1 :=
  Prod.ext (map_one (finGL E a)) (map_one (finGL E b))

theorem actS_eq {S : Set (Pl E)} (φ₁ φ₂ : ∀ w : Pl E, LF a b w) (e : ∀ i : Slot S, (GLw a i.pl × GLw b i.pl) →* Hf E a b)
    (he₁ : ∀ (w : {w // w ∈ S}) (m : GLw a w.1 × GLw b w.1), finH (e (.inl w) m) = (embW a w.1 m.1, embW b w.1 m.2))
    (he₂ : ∀ (w : {w // w ∈ S ∧ IsSplitAt w}) (m : GLw a w.1 × GLw b w.1),
      finH (e (.inr w) m) = (embT a w.1 m.1, embT b w.1 m.2))
    (i : Slot S) (G : H E a b → ℂ) (z : H E a b) :
    actS φ₁ φ₂ i G z = hint (K2 a b i.pl) fun m => sf φ₁ φ₂ i m * G (z * finH (e i m)) := by
  rcases i with w | w
  · change hint (K2 a b w.1) (fun m => φ₁ w.1 m * pairRt a b w.1 m G z) = hint (K2 a b w.1) fun m => φ₁ w.1 m * G (z * finH (e (.inl w) m))
    refine congrArg _ (funext fun m => ?_)
    rw [he₁]
    rfl
  · change hint (K2 a b w.1) (fun m => φ₂ w.1 m * pairRtT a b w.1 m G z) = hint (K2 a b w.1) fun m => φ₂ w.1 m * G (z * finH (e (.inr w) m))
    refine congrArg _ (funext fun m => ?_)
    rw [he₂]
    rfl

theorem finActOf : FinActOf := by
  intro hInt hSl hConv _ E _ _ _ B S hS φ₁ φ₂ h₁ h₂ G hG l hl hfix x
  haveI := B.hν
  haveI := B.hν'
  haveI : BorelSpace (Hf E B.a B.b) := ⟨rfl⟩
  obtain ⟨hmul, hcont, hsep, -, hev, hmem, -⟩ := hSl E B.a B.b S hS
  obtain ⟨e, hec, hpe, hpe', he₁, he₂⟩ := GlobalTheory.T.position_embeddings_exist (E := E) B.a B.b hS
  obtain ⟨U₀, hU₀, hlev⟩ := hG
  obtain ⟨-, hc⟩ := hConv E B S hS
  obtain ⟨hcs, ⟨U₁, hU₁, hinv⟩, -⟩ := hc φ₁ φ₂ h₁ h₂
  obtain ⟨L, hLo, hLe, hLi, hLc, hLu⟩ := GlobalTheory.T.position_level_subgroups_exist (S := S) h₁ h₂
  let p : ∀ i : Slot S, Hf E B.a B.b →* GLw B.a i.pl × GLw B.b i.pl := fun i => MonoidHom.mk' (i.cp B.a B.b) (hmul i)
  let K : Subgroup (Hf E B.a B.b) := (Kf E B.a).prod (Kf E B.b)
  have hKo : IsOpen (K : Set (Hf E B.a B.b)) := by
    rw [Subgroup.coe_prod]
    exact GlobalTheory.CompanionTheory.EulerV.isOpen_Kf.prod GlobalTheory.CompanionTheory.EulerV.isOpen_Kf
  have hKc : IsCompact (K : Set (Hf E B.a B.b)) := by
    rw [Subgroup.coe_prod]
    exact GlobalTheory.CompanionTheory.EulerV.isCompact_Kf.prod GlobalTheory.CompanionTheory.EulerV.isCompact_Kf
  have hKHo : ∀ i : Slot S, IsOpen (K2 B.a B.b i.pl : Set (GLw B.a i.pl × GLw B.b i.pl)) := fun i =>
    (GlobalTheory.CompanionTheory.FinTestTw.isRestrW B.a B.b).isOpen_K i.pl
  have hKHc : ∀ i : Slot S, IsCompact (K2 B.a B.b i.pl : Set (GLw B.a i.pl × GLw B.b i.pl)) := fun i =>
    (GlobalTheory.CompanionTheory.FinTestTw.isRestrW B.a B.b).isCompact_K i.pl
  obtain ⟨V₀, hV₀o, hV₀K, hV₀e, hV₀U⟩ := GlobalTheory.T.restricted_product_embeddings p e K (fun i => K2 B.a B.b i.pl) hcont hec hpe hpe' hsep hmem hKc hKHo U₀ hU₀
  let V : ∀ i : Slot S, Subgroup (GLw B.a i.pl × GLw B.b i.pl) := fun i => V₀ i ⊓ L i
  have hVo : ∀ i, IsOpen (V i : Set (GLw B.a i.pl × GLw B.b i.pl)) := fun i => by
    simp only [V, Subgroup.coe_inf]
    exact (hV₀o i).inter (hLo i)
  let g : Hf E B.a B.b → ℂ := fun h => G (x * finH h)
  have hact := actS_eq φ₁ φ₂ e he₁ he₂
  have hcore := GlobalTheory.T.restricted_product_integral p e K (fun i => K2 B.a B.b i.pl) V (sf φ₁ φ₂) hpe hpe' hsep hev hmem
    (fun i => inf_le_left.trans (hV₀K i)) (fun i => relIndex_ne_zero_of_open (hVo i) (hKHc i))
    (by
      filter_upwards [hV₀e, hLe, hLu] with i a₁ a₂ a₃
      exact ⟨by simp only [V, a₁, a₂, inf_idem], a₃⟩)
    (fun i u hu y => hLi i u hu.2 y)
    (fun i => GlobalTheory.TwTrLin.finite_out_support (hVo i) (hLc i))
    g
    (fun u hu y => by
      have hu₀ : u ∈ U₀ := hV₀U u fun i => (hu i).1
      simp only [g]
      rw [finH_mul, ← mul_assoc]
      exact hlev u hu₀ _)
    l hl
    (fun i hi => funext fun y => by
      have h1 := hact i G (x * finH y)
      rw [hfix i hi] at h1
      simp only [g, finH_mul, ← mul_assoc]
      exact h1.symm)
  have hfold : ∀ (l' : List (Slot S)) (y : Hf E B.a B.b),
      l'.foldr (fun i g' x => hint (K2 B.a B.b i.pl) fun m => sf φ₁ φ₂ i m * g' (x * e i m)) g y =
        l'.foldr (fun i g' => actS φ₁ φ₂ i g') G (x * finH y) := by
    intro l'
    induction l' with
    | nil => intro y; rfl
    | cons i l' ih =>
      intro y
      simp only [List.foldr_cons]
      rw [hact]
      refine congrArg _ (funext fun m => ?_)
      rw [ih, finH_mul, mul_assoc]
  have hint₁ := hInt (Hf E B.a B.b) B.ν K (U₀ ⊓ U₁) (fun h => finFn S φ₁ φ₂ h * g h) hKo hKc
    (by rw [Subgroup.coe_inf]; exact hU₀.inter hU₁) hcs.mul_right
    (fun u hu y => by
      have e1 := (hinv u hu.2 y).2
      simp only [g]
      rw [e1, finH_mul, ← mul_assoc, hlev u hu.1])
    inferInstance
  have hF : (fun h => finFn S φ₁ φ₂ h * g h) = fun h => (∏ᶠ i : Slot S, sf φ₁ φ₂ i (p i h)) * g h :=
    funext fun h => by rw [GlobalTheory.T.finite_test_function_product h₁ h₂]; rfl
  have hfin := hfold l 1
  rw [finH_one, mul_one] at hfin
  rw [← hfin, ← hcore, ← hF]
  exact hint₁

end GlobalTheory.CompanionTheory.FinActS

end
