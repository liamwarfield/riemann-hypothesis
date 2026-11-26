module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosDefQuadraticFormHom

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFreeOfPositiveDefiniteFormBoundedRank
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFreeOfPositiveDefiniteFormBoundedRank
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem finite_free_of_definite_form_of_rank_le :
    ∀ (H : Type) [AddCommGroup H] (Q : H → ℤ), (∀ f g, Q (f + g) + Q (f - g) = 2 * Q f + 2 * Q g) → (∀ f, 0 ≤ Q f) → (∀ f, Q f = 0 → f = 0) → ∀ r : ℕ, (∀ (n : ℕ) (u : Fin n → H), LinearIndependent ℤ u → n ≤ r) → Module.Finite ℤ H ∧ Module.Free ℤ H ∧ Module.finrank ℤ H ≤ r := by
  intro H _ Q hQ hpos hdef r hr
  classical
  have h0 : Q 0 = 0 := by
    have := hQ 0 0
    simp only [add_zero, sub_zero] at this
    omega
  have htf : ∀ (k : ℤ) (f : H), k ≠ 0 → k • f = 0 → f = 0 := by
    intro k f hk hkf
    apply hdef
    have h1 := parallelogram_zsmul Q hQ k f
    rw [hkf, h0] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left (pow_ne_zero 2 hk)
  let P : ℕ → Prop := fun n => ∃ u : Fin n → H, LinearIndependent ℤ u
  obtain ⟨n, hn⟩ : ∃ n, n = Nat.findGreatest P r := ⟨_, rfl⟩
  have hPn : P n := hn ▸
    Nat.findGreatest_spec (P := P) (m := 0) (Nat.zero_le r) ⟨Fin.elim0, linearIndependent_empty_type⟩
  obtain ⟨u, hu⟩ := hPn
  have hmax : ¬ P (n + 1) := by
    rintro ⟨v, hv⟩
    have hlt : Nat.findGreatest P r < n + 1 := by omega
    exact Nat.findGreatest_is_greatest (P := P) (n := r) hlt (hr _ v hv) ⟨v, hv⟩
  have hspan : ∀ h : H, ∃ k : ℕ, 0 < k ∧ ∃ m : Fin n → ℤ, k • h = ∑ i, m i • u i := by
    intro h
    by_contra hne
    push_neg at hne
    apply hmax
    refine ⟨Fin.cons h u, LinearIndependent.finCons' h u hu fun c y hy hcy => ?_⟩
    by_contra hc
    obtain ⟨m, hm⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hy
    have hpos' : 0 < c.natAbs := Int.natAbs_pos.2 hc
    rcases Int.natAbs_eq c with hc' | hc'
    · apply hne c.natAbs hpos' (fun i => - m i)
      rw [← natCast_zsmul, ← hc']
      simp only [neg_smul, Finset.sum_neg_distrib, hm]
      exact eq_neg_of_add_eq_zero_left hcy
    · apply hne c.natAbs hpos' m
      rw [← natCast_zsmul, hm]
      have : c • h = - ((c.natAbs : ℤ) • h) := by
        conv_lhs => rw [hc']
        rw [neg_smul]
      rw [this] at hcy
      exact (neg_add_eq_zero.mp hcy)
  obtain ⟨e, he, hdiv⟩ := exists_dvd_coords_of_definite_form H ⊤ Q hQ hpos
    (fun f _ => hdef f) n u (fun _ => trivial) hu
  have hmem : ∀ h : H, (e : ℤ) • h ∈ Submodule.span ℤ (Set.range u) := by
    intro h
    obtain ⟨k, hk, m, hkm⟩ := hspan h
    have hd := hdiv k m h trivial hkm
    choose m' hm' using hd
    have hz : (k : ℤ) • ((e : ℤ) • h - ∑ i, m' i • u i) = 0 := by
      rw [smul_sub, smul_comm (k : ℤ) (e : ℤ) h, natCast_zsmul h k, hkm, Finset.smul_sum, Finset.smul_sum,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [smul_smul, smul_smul, ← hm' i, sub_self]
    have := htf k _ (by exact_mod_cast hk.ne') hz
    rw [sub_eq_zero.mp this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let f : H →ₗ[ℤ] Submodule.span ℤ (Set.range u) :=
    LinearMap.codRestrict _ ((e : ℤ) • LinearMap.id) hmem
  have hinj : Function.Injective f := by
    intro a b hab
    have h' : (e : ℤ) • a = (e : ℤ) • b := congrArg Subtype.val hab
    have : (e : ℤ) • (a - b) = 0 := by rw [smul_sub, h', sub_self]
    exact sub_eq_zero.mp (htf e _ (by exact_mod_cast he.ne') this)
  have : Module.Finite ℤ (Submodule.span ℤ (Set.range u)) :=
    Module.Finite.span_of_finite ℤ (Set.finite_range u)
  have hfin : Module.Finite ℤ H := Module.Finite.of_injective f hinj
  have : Module.IsTorsionFree ℤ H := Module.IsTorsionFree.of_smul_eq_zero fun k x hkx => by
    by_cases hk : k = 0
    · exact Or.inl hk
    · exact Or.inr (htf k x hk hkx)
  have hfree : Module.Free ℤ H := Module.free_of_finite_type_torsion_free'
  refine ⟨hfin, hfree, ?_⟩
  exact hr _ _ (Module.finBasis ℤ H).linearIndependent

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFreeOfPositiveDefiniteFormBoundedRankStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_free_of_positiveDefinite_form_bounded_rank : ∀ (H : Type) [AddCommGroup H] (Q : H → ℤ), (∀ f g, Q (f + g) + Q (f - g) = 2 * Q f + 2 * Q g) → (∀ f, 0 ≤ Q f) → (∀ f, Q f = 0 → f = 0) → ∀ r : ℕ, (∀ (n : ℕ) (u : Fin n → H), LinearIndependent ℤ u → n ≤ r) → Module.Finite ℤ H ∧ Module.Free ℤ H ∧ Module.finrank ℤ H ≤ r := by
  first | exact @GlobalTheory.finite_free_of_definite_form_of_rank_le | exact GlobalTheory.finite_free_of_definite_form_of_rank_le | (intros; apply GlobalTheory.finite_free_of_definite_form_of_rank_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulEqOfTateModuleMapEqSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulEqOfTateModuleMapEqSmul
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem exists_nsmul_eq_of_tmap_eq_smul : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 →
    ∀ (A B : AbVar K) (f : A ⟶ B) (φ : Tl l A →ₗ[ℤ_[l]] Tl l B),
      tmap l A B f = (l : ℤ_[l]) • φ → ∃ g : A ⟶ B, f = l • g := by
  intro K _ l _ hl A B f φ hf
  refine exists_nsmul_eq_of_kills_torsion K A B f l hl fun x hx => ?_
  obtain ⟨t, ht⟩ := (tl_lev_surj_ker K l A 1).1 x (by rwa [pow_one])
  have h1 : (tmap l A B f t).lev 1 = x ≫ f.hom := by rw [lev_tmap, ht]
  rw [← h1, hf, LinearMap.smul_apply]
  exact ((tl_lev_surj_ker K l B 1).2 _).2 ⟨φ t, by rw [pow_one]⟩

end GlobalTheory.AV.AbVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulEqOfTateModuleMapEqSmulStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nsmul_eq_of_tateModuleMap_eq_smul : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A B : AbVar K) (f : A ⟶ B) (φ : Tl l A →ₗ[ℤ_[l]] Tl l B), tmap l A B f = (l : ℤ_[l]) • φ → ∃ g : A ⟶ B, f = l • g := by
  first | (exact @GlobalTheory.AV.AbVar.exists_nsmul_eq_of_tmap_eq_smul) | (exact GlobalTheory.AV.AbVar.exists_nsmul_eq_of_tmap_eq_smul) | (intros; apply GlobalTheory.AV.AbVar.exists_nsmul_eq_of_tmap_eq_smul  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankLeFinrankOfInjectiveModPrimePosDefForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftBaseChangePadicIntInjectiveSaturatedOfModL
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftBaseChangePadicIntInjectiveSaturatedOfModL
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatticeModL

theorem exists_one_tmul_add_smul (l : ℕ) [Fact l.Prime] (H : Type) [AddCommGroup H]
    (x : ℤ_[l] ⊗[ℤ] H) :
    ∃ (h : H) (y : ℤ_[l] ⊗[ℤ] H), x = (1 : ℤ_[l]) ⊗ₜ h + (l : ℤ_[l]) • y := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul a h =>
    obtain ⟨c, hc⟩ : ∃ c : ℤ_[l], a - (a.zmodRepr : ℤ_[l]) = (l : ℤ_[l]) * c := by
      have := PadicInt.sub_zmodRepr_mem a
      rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at this
      exact this
    refine ⟨(a.zmodRepr : ℤ) • h, c ⊗ₜ h, ?_⟩
    have ha : a = ((a.zmodRepr : ℤ) : ℤ_[l]) + (l : ℤ_[l]) * c := by
      rw [← hc]; push_cast; ring
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
      smul_eq_mul, zsmul_eq_mul, _root_.mul_one, ← TensorProduct.add_tmul, ← ha]
  | add x y hx hy =>
    obtain ⟨h₁, y₁, rfl⟩ := hx
    obtain ⟨h₂, y₂, rfl⟩ := hy
    exact ⟨h₁ + h₂, y₁ + y₂, by rw [TensorProduct.tmul_add, smul_add]; abel⟩

end GlobalTheory.LatticeModL


open GlobalTheory.LatticeModL in
theorem GlobalTheory.latticeMap_liftBaseChange_injective_saturated :
    ∀ (l : ℕ) [Fact l.Prime] (H T : Type) [AddCommGroup H] [Module.Finite ℤ H] [Module.Free ℤ H]
      [AddCommGroup T] [Module ℤ_[l] T], (∀ t : T, (l : ℤ_[l]) • t = 0 → t = 0) →
      ∀ φ : H →+ T, (∀ (h : H) (t : T), φ h = (l : ℤ_[l]) • t → ∃ h' : H, h = l • h') →
      Function.Injective (φ.toIntLinearMap.liftBaseChange ℤ_[l]) ∧
      ∀ t : T, (l : ℤ_[l]) • t ∈ LinearMap.range (φ.toIntLinearMap.liftBaseChange ℤ_[l]) →
        t ∈ LinearMap.range (φ.toIntLinearMap.liftBaseChange ℤ_[l]) := by
  intro l _ H T _ _ _ _ _ htor φ hsat
  set F := φ.toIntLinearMap.liftBaseChange ℤ_[l] with hFdef
  have hF : ∀ h, F ((1 : ℤ_[l]) ⊗ₜ h) = φ h := by
    intro h; simp [F]
  have key : ∀ (x : ℤ_[l] ⊗[ℤ] H) (t : T), F x = (l : ℤ_[l]) • t →
      ∃ x', x = (l : ℤ_[l]) • x' := by
    intro x t hx
    obtain ⟨h, y, rfl⟩ := exists_one_tmul_add_smul l H x
    rw [map_add (f := _), map_smul, hF] at hx
    have h1 : φ h = (l : ℤ_[l]) • (t - F y) := by rw [smul_sub, ← hx]; abel
    obtain ⟨h', rfl⟩ := hsat h _ h1
    refine ⟨(1 : ℤ_[l]) ⊗ₜ h' + y, ?_⟩
    rw [smul_add, TensorProduct.tmul_smul]
    simp only [Nat.cast_smul_eq_nsmul]
  have hl : (l : ℤ_[l]) ∈ IsLocalRing.maximalIdeal ℤ_[l] := by
    rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot]
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal ℤ_[l]) _
      (IsNoetherian.noetherian _) ?_ (IsLocalRing.maximalIdeal_le_jacobson _)
    intro x hx
    rw [LinearMap.mem_ker] at hx
    obtain ⟨x', rfl⟩ := key x 0 (by rw [hx, smul_zero])
    have : F x' = 0 := htor _ (by rw [← map_smul, hx])
    exact Submodule.smul_mem_smul hl this
  · rintro t ⟨x, hx⟩
    obtain ⟨x', rfl⟩ := key x t hx
    refine ⟨x', ?_⟩
    have : (l : ℤ_[l]) • (F x' - t) = 0 := by rw [smul_sub, ← map_smul, hx, sub_self]
    exact sub_eq_zero.mp (htor _ this)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftBaseChangePadicIntInjectiveSaturatedOfModLStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftBaseChange_padicInt_injective_saturated_of_modL : ∀ (l : ℕ) [Fact l.Prime] (H T : Type) [AddCommGroup H] [Module.Finite ℤ H] [Module.Free ℤ H] [AddCommGroup T] [Module ℤ_[l] T], (∀ t : T, (l : ℤ_[l]) • t = 0 → t = 0) → ∀ φ : H →+ T, (∀ (h : H) (t : T), φ h = (l : ℤ_[l]) • t → ∃ h' : H, h = l • h') → Function.Injective (φ.toIntLinearMap.liftBaseChange ℤ_[l]) ∧ ∀ t : T, (l : ℤ_[l]) • t ∈ LinearMap.range (φ.toIntLinearMap.liftBaseChange ℤ_[l]) → t ∈ LinearMap.range (φ.toIntLinearMap.liftBaseChange ℤ_[l]) := by
  first | (exact @GlobalTheory.latticeMap_liftBaseChange_injective_saturated) | (exact GlobalTheory.latticeMap_liftBaseChange_injective_saturated) | (intros; apply GlobalTheory.latticeMap_liftBaseChange_injective_saturated  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankLeFinrankOfInjectiveModPrimePosDefForm
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

def satSpanFamily {H : Type} [AddCommGroup H] {n : ℕ} (u : Fin n → H) : AddSubgroup H where
  carrier := {h | ∃ k : ℤ, k ≠ 0 ∧ k • h ∈ Submodule.span ℤ (Set.range u)}
  zero_mem' := ⟨1, one_ne_zero, by simp⟩
  add_mem' := by
    rintro a b ⟨k, hk, ha⟩ ⟨m, hm, hb⟩
    refine ⟨k * m, mul_ne_zero hk hm, ?_⟩
    rw [smul_add, mul_smul, mul_smul, smul_comm k m a]
    exact add_mem (Submodule.smul_mem _ m ha) (Submodule.smul_mem _ k hb)
  neg_mem' := by
    rintro a ⟨k, hk, ha⟩
    exact ⟨k, hk, by rw [smul_neg]; exact neg_mem ha⟩

theorem rank_le_finrank_of_injective_mod_prime : ∀ (l : ℕ) [Fact l.Prime] (H T : Type) [AddCommGroup H] [AddCommGroup T] [Module ℤ_[l] T] [Module.Finite ℤ_[l] T] [Module.Free ℤ_[l] T] (Q : H → ℤ), (∀ f g, Q (f + g) + Q (f - g) = 2 * Q f + 2 * Q g) → (∀ f, 0 ≤ Q f) → (∀ f, Q f = 0 → f = 0) → ∀ φ : H →+ T, (∀ (h : H) (t : T), φ h = (l : ℤ_[l]) • t → ∃ h' : H, h = l • h') → ∀ (n : ℕ) (u : Fin n → H), LinearIndependent ℤ u → n ≤ Module.finrank ℤ_[l] T := by
  intro l _ H T _ _ _ _ _ Q hpar hnn hdef φ hφ n u hu
  classical
  set M := satSpanFamily u with hMdef
  have memM : ∀ h, h ∈ M ↔ ∃ k : ℤ, k ≠ 0 ∧ k • h ∈ Submodule.span ℤ (Set.range u) :=
    fun h => Iff.rfl
  have hbound : ∀ (m : ℕ) (v : Fin m → M), LinearIndependent ℤ v → m ≤ n := by
    intro m v hv
    choose k hk hks using fun j => (memM (v j : H)).1 (v j).2
    let w : Fin m → Submodule.span ℤ (Set.range u) := fun j => ⟨k j • (v j : H), hks j⟩
    have hw : LinearIndependent ℤ w := by
      rw [Fintype.linearIndependent_iff] at hv ⊢
      intro g hg j
      have h1 : ∑ i, (g i * k i) • v i = 0 := by
        apply Subtype.ext
        have := congrArg Subtype.val hg
        simpa [w, mul_smul] using this
      exact (mul_eq_zero.1 (hv _ h1 j)).resolve_right (hk j)
    haveI : Module.Finite ℤ (Submodule.span ℤ (Set.range u)) :=
      Module.Finite.span_of_finite ℤ (Set.finite_range u)
    have := hw.fintype_card_le_finrank
    rw [finrank_span_eq_card hu] at this
    simpa using this
  obtain ⟨hfin, hfree, -⟩ := GlobalTheory.finite_free_of_definite_form_of_rank_le M (fun x => Q x)
    (fun f g => by simpa using hpar f g) (fun f => hnn f) (fun f hf => Subtype.ext (hdef _ hf)) n hbound
  haveI := hfin
  haveI := hfree
  let ψ : M →+ T := φ.comp M.subtype
  have hlne : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have hψ : ∀ (h : M) (t : T), ψ h = (l : ℤ_[l]) • t → ∃ h' : M, h = l • h' := by
    intro h t ht
    obtain ⟨h', hh'⟩ := hφ (h : H) t ht
    obtain ⟨k, hk, hks⟩ := (memM (h : H)).1 h.2
    refine ⟨⟨h', k * l, mul_ne_zero hk (by exact_mod_cast hlne), ?_⟩, Subtype.ext ?_⟩
    · rw [mul_smul, natCast_zsmul, ← hh']
      exact hks
    · simp [hh']
  have htor : ∀ t : T, (l : ℤ_[l]) • t = 0 → t = 0 := by
    intro t ht
    have hl : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hlne
    exact (smul_eq_zero.1 ht).resolve_left hl
  obtain ⟨hinj, -⟩ := GlobalTheory.T.liftBaseChange_padicInt_injective_saturated_of_modL l M T htor ψ hψ
  have h1 := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_baseChange] at h1
  let v : Fin n → M := fun i => ⟨u i, 1, one_ne_zero, by
    simpa using Submodule.subset_span (Set.mem_range_self i)⟩
  have hv : LinearIndependent ℤ v :=
    LinearIndependent.of_comp M.subtype.toIntLinearMap (by
      have e : (M.subtype.toIntLinearMap : M →ₗ[ℤ] H) ∘ v = u := funext fun i => rfl
      rw [e]; exact hu)
  have h2 := hv.fintype_card_le_finrank
  simp only [Fintype.card_fin] at h2
  omega

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankLeFinrankOfInjectiveModPrimePosDefFormStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_le_finrank_of_injective_mod_prime_posDef_form : ∀ (l : ℕ) [Fact l.Prime] (H T : Type) [AddCommGroup H] [AddCommGroup T] [Module ℤ_[l] T] [Module.Finite ℤ_[l] T] [Module.Free ℤ_[l] T] (Q : H → ℤ), (∀ f g, Q (f + g) + Q (f - g) = 2 * Q f + 2 * Q g) → (∀ f, 0 ≤ Q f) → (∀ f, Q f = 0 → f = 0) → ∀ φ : H →+ T, (∀ (h : H) (t : T), φ h = (l : ℤ_[l]) • t → ∃ h' : H, h = l • h') → ∀ (n : ℕ) (u : Fin n → H), LinearIndependent ℤ u → n ≤ Module.finrank ℤ_[l] T := by
  first | (exact @GlobalTheory.rank_le_finrank_of_injective_mod_prime) | (exact GlobalTheory.rank_le_finrank_of_injective_mod_prime) | (intros; apply GlobalTheory.rank_le_finrank_of_injective_mod_prime  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFiniteFreeFinrankLeFourMulDim
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem hom_finite_free_rank_le_of_prime (K : Type) [Field K] (l : ℕ) [Fact l.Prime]
    (hl : (l : K) ≠ 0) (A B : AbVar K) :
    Module.Finite ℤ (A ⟶ B) ∧ Module.Free ℤ (A ⟶ B) ∧
      Module.finrank ℤ (A ⟶ B) ≤ 4 * A.dim * B.dim := by
  obtain ⟨hFA, hfA, hrA, -, -⟩ := GlobalTheory.T.tateModule_free_finrank_two_mul_dim K l hl A
  obtain ⟨hFB, hfB, hrB, -, -⟩ := GlobalTheory.T.tateModule_free_finrank_two_mul_dim K l hl B
  obtain ⟨Q, hpar, hpos, hdef⟩ := GlobalTheory.T.exists_posDef_quadraticForm_hom K A B
  have hrT : Module.finrank ℤ_[l] (Tl l A →ₗ[ℤ_[l]] Tl l B) = 4 * A.dim * B.dim := by
    rw [Module.finrank_linearMap, hrA, hrB]; ring
  refine GlobalTheory.T.finite_free_of_positiveDefinite_form_bounded_rank (A ⟶ B) Q hpar hpos hdef (4 * A.dim * B.dim) ?_
  intro n u hu
  rw [← hrT]
  refine GlobalTheory.T.rank_le_finrank_of_injective_mod_prime_posDef_form l (A ⟶ B) (Tl l A →ₗ[ℤ_[l]] Tl l B) Q hpar hpos hdef (tmap l A B) ?_ n u hu
  intro f φ hφ
  exact GlobalTheory.T.exists_nsmul_eq_of_tateModuleMap_eq_smul K l hl A B f φ hφ

theorem hom_finite_free_rank_le : ∀ (K : Type) [Field K] (A B : AbVar K),
    Module.Finite ℤ (A ⟶ B) ∧ Module.Free ℤ (A ⟶ B) ∧
      Module.finrank ℤ (A ⟶ B) ≤ 4 * A.dim * B.dim := by
  intro K _ A B
  by_cases h2 : ((2 : ℕ) : K) = 0
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h3 : ((3 : ℕ) : K) ≠ 0 := by
      have : ((3 : ℕ) : K) = ((2 : ℕ) : K) + 1 := by push_cast; ring
      rw [this, h2, zero_add]; exact one_ne_zero
    exact hom_finite_free_rank_le_of_prime K 3 h3 A B
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact hom_finite_free_rank_le_of_prime K 2 h2 A B

end GlobalTheory.AV.AbVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFiniteFreeFinrankLeFourMulDimStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hom_finite_free_finrank_le_four_mul_dim : ∀ (K : Type) [Field K] (A B : AbVar K), Module.Finite ℤ (A ⟶ B) ∧ Module.Free ℤ (A ⟶ B) ∧ Module.finrank ℤ (A ⟶ B) ≤ 4 * A.dim * B.dim := by
  first | (exact @GlobalTheory.AV.AbVar.hom_finite_free_rank_le) | (exact GlobalTheory.AV.AbVar.hom_finite_free_rank_le) | (intros; apply GlobalTheory.AV.AbVar.hom_finite_free_rank_le  <;> assumption)
end
