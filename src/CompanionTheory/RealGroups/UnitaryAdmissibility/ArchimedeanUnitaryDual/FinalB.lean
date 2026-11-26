module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StatementCommutative
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ProjectionStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeAlgebraStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ModularityStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DictionaryStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FactorizationStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CartanDecompositionGL
public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.ArchimedeanDenseStabilizers.StabOfMemLevelOpen
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ArchimedeanPrincipalSeries
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StTensor
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PlaneOfHenselAndPairing
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SplittingOfSandwichAndPairing
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.WittStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DecompositionOfFrameWittTorus
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IwahoriStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LatticeCongruenceSubgroupsOpenCompact
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsometricLatticeCongruenceSubgroups
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StTensorStatement

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HenselStatement
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HenselStatement
open CompanionTheory.Rg.FlB

namespace GlobalTheory.CompanionTheory.LocalHensel

theorem stHensel_holds : StHensel := by
  intro L _ _ _ s hs c d hsc hsd hc hd
  obtain ⟨-, hn, -⟩ := hs
  have hcont : Continuous s := (AddMonoidHomClass.isometry_of_norm s hn).continuous
  have hXc : IsClosed {u : L | s u = u ∧ ‖u‖ ≤ 1} :=
    (isClosed_eq hcont continuous_id).inter (isClosed_le continuous_norm continuous_const)
  haveI : CompleteSpace {u : L | s u = u ∧ ‖u‖ ≤ 1} := hXc.completeSpace_coe
  haveI : Nonempty {u : L | s u = u ∧ ‖u‖ ≤ 1} := ⟨⟨0, map_zero s, by simp⟩⟩
  have hmaps : ∀ u : L, s u = u ∧ ‖u‖ ≤ 1 → s (-d - c * u ^ 2) = -d - c * u ^ 2 ∧
      ‖-d - c * u ^ 2‖ ≤ 1 := by
    rintro u ⟨hu, hu1⟩
    refine ⟨by simp only [map_sub, map_neg, map_mul, map_pow, hu, hsc, hsd], ?_⟩
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by simpa using hd) ?_)
    rw [norm_neg, norm_mul, norm_pow]
    have h2 : ‖u‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hu1
    exact mul_le_one₀ hc.le (by positivity) h2
  let F : {u : L | s u = u ∧ ‖u‖ ≤ 1} → {u : L | s u = u ∧ ‖u‖ ≤ 1} :=
    fun u => ⟨-d - c * (u : L) ^ 2, hmaps u u.2⟩
  have hF : ContractingWith ‖c‖₊ F := by
    refine ⟨by exact_mod_cast hc, LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    have hxy : ‖(x : L) + y‖ ≤ 1 :=
      (IsUltrametricDist.norm_add_le_max _ _).trans (max_le x.2.2 y.2.2)
    have key : (-d - c * (x : L) ^ 2) - (-d - c * (y : L) ^ 2)
        = -(c * (((x : L) + y) * ((x : L) - y))) := by ring
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    change ‖(-d - c * (x : L) ^ 2) - (-d - c * (y : L) ^ 2)‖ ≤ _
    rw [key, norm_neg, norm_mul, norm_mul, coe_nnnorm]
    have h0 : 0 ≤ ‖(x : L) - y‖ := norm_nonneg _
    exact mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_left h0 hxy) (norm_nonneg _)
  have hfix := hF.fixedPoint_isFixedPt
  set u := ContractingWith.fixedPoint F hF with hu
  have hval : -d - c * (u : L) ^ 2 = u := congrArg Subtype.val hfix
  refine ⟨u, u.2.1, u.2.2, ?_⟩
  linear_combination -hval

end GlobalTheory.CompanionTheory.LocalHensel
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HenselStatementStatement
open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.HenselStatement : StHensel := by
  first | exact @GlobalTheory.CompanionTheory.LocalHensel.stHensel_holds | exact GlobalTheory.CompanionTheory.LocalHensel.stHensel_holds | (intros; apply GlobalTheory.CompanionTheory.LocalHensel.stHensel_holds <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FrameOfAnisotropicPlaneSplitting
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FrameOfAnisotropicPlaneSplitting
open CompanionTheory.Rg.FlB

noncomputable section

namespace GlobalTheory.CompanionTheory.HermFrame

section Steps

variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
  {s : L →+* L} {h : V → V → L}

theorem herm_smul_left (hh : IsHerm s h) (a : L) (x y : V) : h (a • x) y = s a * h x y := by
  obtain ⟨_, h2, h3, _⟩ := hh
  rw [h3 y (a • x), h2, map_mul, ← h3 y x]

theorem herm_symm_zero (hh : IsHerm s h) {x y : V} (hxy : h x y = 0) : h y x = 0 := by
  rw [hh.2.2.1 x y, hxy, map_zero]

theorem herm_right_zero (hh : IsHerm s h) (x : V) : h x 0 = 0 := by
  have := hh.2.1 (0 : L) x 0
  simpa using this

def orthPair (hh : IsHerm s h) (e f : V) : Submodule L V where
  carrier := {x | h e x = 0 ∧ h f x = 0}
  add_mem' := by
    intro a b ha hb
    exact ⟨by rw [hh.1, ha.1, hb.1, add_zero], by rw [hh.1, ha.2, hb.2, add_zero]⟩
  zero_mem' := ⟨herm_right_zero hh e, herm_right_zero hh f⟩
  smul_mem' := by
    intro c x hx
    exact ⟨by rw [hh.2.1, hx.1, mul_zero], by rw [hh.2.1, hx.2, mul_zero]⟩

theorem frame_cons (hh : IsHerm s h) {δ : L} {e f : V} {U : Submodule L V}
    (hU : ∀ x, x ∈ U ↔ h e x = 0 ∧ h f x = 0) (hee : h e e = 0) (hff : h f f = 0) (hef : h e f = δ)
    (hdec : ∀ x, ∃ (a b : L), ∃ w ∈ U, x = a • e + b • f + w) {l : ℕ} {e' f' : Fin l → U}
    {W' : Submodule L U} (hfr : IsFrame (fun x y : U => h x y) δ e' f' W') :
    IsFrame h δ (Fin.cons e fun i => (e' i : V) : Fin (l + 1) → V)
      (Fin.cons f fun i => (f' i : V) : Fin (l + 1) → V) (W'.map U.subtype) := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hfr
  have heU : ∀ x ∈ U, h e x = 0 := fun x hx => ((hU x).1 hx).1
  have hfU : ∀ x ∈ U, h f x = 0 := fun x hx => ((hU x).1 hx).2
  have heU' : ∀ x ∈ U, h x e = 0 := fun x hx => herm_symm_zero hh (heU x hx)
  have hfU' : ∀ x ∈ U, h x f = 0 := fun x hx => herm_symm_zero hh (hfU x hx)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simpa using hee
      | succ j => simpa using heU _ (e' j).2
    | succ i =>
      induction j using Fin.cases with
      | zero => simpa using heU' _ (e' i).2
      | succ j => simpa using a1 i j
  · intro i j
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simpa using hff
      | succ j => simpa using hfU _ (f' j).2
    | succ i =>
      induction j using Fin.cases with
      | zero => simpa using hfU' _ (f' i).2
      | succ j => simpa using a2 i j
  · intro i j
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simpa using hef
      | succ j =>
        simpa [Ne.symm (Fin.succ_ne_zero j)] using heU _ (f' j).2
    | succ i =>
      induction j using Fin.cases with
      | zero => simpa [Fin.succ_ne_zero i] using hfU' _ (e' i).2
      | succ j => simpa using a3 i j
  · intro w hw i
    obtain ⟨w', hw', rfl⟩ := Submodule.mem_map.1 hw
    induction i using Fin.cases with
    | zero => simpa using And.intro (heU _ w'.2) (hfU _ w'.2)
    | succ i => simpa using a4 w' hw' i
  · intro w hw h0
    obtain ⟨w', hw', rfl⟩ := Submodule.mem_map.1 hw
    have : w' = 0 := a5 w' hw' h0
    simp [this]
  · intro x
    obtain ⟨a, b, w, hw, rfl⟩ := hdec x
    obtain ⟨a', b', w', hw', hEq⟩ := a6 ⟨w, hw⟩
    refine ⟨Fin.cons a a', Fin.cons b b', U.subtype w', Submodule.mem_map_of_mem hw', ?_⟩
    have hw2 : w = ∑ i, a' i • (e' i : V) + ∑ i, b' i • (f' i : V) + (w' : V) := by
      have := congrArg Subtype.val hEq
      simpa using this
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Submodule.subtype_apply]
    rw [hw2]
    abel

theorem adapted_cons {U : Submodule L V} {e f : V} {l : ℕ} {e' f' : Fin l → U} {W' : Submodule L U}
    {u0 : L} {u' : Fin l → L} {Λ : AddSubgroup V}
    (hsp : ∀ (a b : L), ∀ w ∈ U, (a • e + b • f + w ∈ Λ ↔ ‖a‖ ≤ ‖u0‖ ∧ ‖b‖ ≤ ‖u0‖⁻¹ ∧ w ∈ Λ))
    (had : IsAdapted (fun x y : U => h x y) e' f' W' u' (Λ.comap U.subtype.toAddMonoidHom)) :
    IsAdapted h (Fin.cons e fun i => (e' i : V) : Fin (l + 1) → V)
      (Fin.cons f fun i => (f' i : V) : Fin (l + 1) → V) (W'.map U.subtype)
      (Fin.cons u0 u' : Fin (l + 1) → L) Λ := by
  intro a b w hw
  obtain ⟨w', hw', rfl⟩ := Submodule.mem_map.1 hw
  have hc := had (fun i => a i.succ) (fun i => b i.succ) w' hw'
  obtain ⟨w0, hw0⟩ : ∃ w0 : U, w0 = ∑ i, a i.succ • e' i + ∑ i, b i.succ • f' i + w' := ⟨_, rfl⟩
  rw [← hw0] at hc
  have hval : (w0 : V) = ∑ i, a i.succ • (e' i : V) + ∑ i, b i.succ • (f' i : V) + (w' : V) := by
    rw [hw0]
    simp
  have hrw : ∑ i, a i • (Fin.cons e (fun i => (e' i : V)) : Fin (l + 1) → V) i +
      ∑ i, b i • (Fin.cons f (fun i => (f' i : V)) : Fin (l + 1) → V) i + U.subtype w' =
      a 0 • e + b 0 • f + (w0 : V) := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, hval]
    simp only [Fin.cons_zero, Fin.cons_succ, Submodule.subtype_apply]
    abel
  have hc' : (w0 : V) ∈ Λ ↔ (∀ i, ‖a i.succ‖ ≤ ‖u' i‖) ∧ (∀ i, ‖b i.succ‖ ≤ ‖u' i‖⁻¹) ∧
      ‖h w' w'‖ ≤ 1 := hc
  rw [hrw, hsp _ _ _ w0.2, hc']
  simp only [Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, Submodule.subtype_apply]
  tauto

end Steps

theorem exists_adapted_frame_with_unit_scaling (hA : StAniso) (hP : StPlane) (hS : StSplit)
    (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L] [CharZero L]
    (s : L →+* L) (hs : IsInv s) (δ : L) (hδ : IsDelta s δ) (n : ℕ) :
    ∀ (V : Type) [AddCommGroup V] [Module L V] [FiniteDimensional L V] (h : V → V → L),
      Module.finrank L V = n → IsHerm s h → ∀ Λ Λ' : AddSubgroup V, IsMax h Λ → IsMax h Λ' →
      ∃ (l : ℕ) (e f : Fin l → V) (W : Submodule L V) (u : Fin l → L), (∀ i, u i ≠ 0) ∧
        IsFrame h δ e f W ∧ IsAdapted h e f W (fun _ => 1) Λ ∧ IsAdapted h e f W u Λ' := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ h hn hh Λ Λ' hΛ hΛ'
  by_cases hiso : ∃ x, x ≠ 0 ∧ h x x = 0
  · obtain ⟨e, f, u, hu, hee, hff, hef, he, hf, hue, hvf⟩ :=
      hP L s hs δ hδ V h hh hiso Λ Λ' hΛ hΛ'
    have hUm : ∀ x, x ∈ orthPair hh e f ↔ h e x = 0 ∧ h f x = 0 := fun x => Iff.rfl
    obtain ⟨hUh, hdec, hUtop, hmax⟩ := hS L s hs δ hδ V h hh e f (orthPair hh e f) hee hff hef hUm
    have hsu : s u ≠ 0 := (map_ne_zero s).2 hu
    have hee' : h (u • e) (u • e) = 0 := by
      rw [herm_smul_left hh, hh.2.1, hee, mul_zero, mul_zero]
    have hff' : h ((s u)⁻¹ • f) ((s u)⁻¹ • f) = 0 := by
      rw [herm_smul_left hh, hh.2.1, hff, mul_zero, mul_zero]
    have hef' : h (u • e) ((s u)⁻¹ • f) = δ := by
      rw [herm_smul_left hh, hh.2.1, hef, ← mul_assoc, mul_inv_cancel₀ hsu, one_mul]
    have hUm' : ∀ x, x ∈ orthPair hh e f ↔ h (u • e) x = 0 ∧ h ((s u)⁻¹ • f) x = 0 := by
      intro x
      rw [hUm, herm_smul_left hh, herm_smul_left hh]
      have hsi' : s ((s u)⁻¹) ≠ 0 := (map_ne_zero s).2 (inv_ne_zero hsu)
      simp [hsu, hsi']
    obtain ⟨-, -, -, hmax'⟩ :=
      hS L s hs δ hδ V h hh (u • e) ((s u)⁻¹ • f) (orthPair hh e f) hee' hff' hef' hUm'
    obtain ⟨m1, p1⟩ := hmax Λ hΛ he hf
    obtain ⟨m2, p2⟩ := hmax' Λ' hΛ' hue hvf
    have hlt : Module.finrank L (orthPair hh e f) < n := hn ▸ Submodule.finrank_lt hUtop
    obtain ⟨l, e', f', W', u', hu', hfr, ad1, ad2⟩ :=
      ih _ hlt (orthPair hh e f) (fun x y => h x y) rfl hUh _ _ m1 m2
    have hsp1 : ∀ (a b : L), ∀ w ∈ orthPair hh e f,
        (a • e + b • f + w ∈ Λ ↔ ‖a‖ ≤ ‖(1 : L)‖ ∧ ‖b‖ ≤ ‖(1 : L)‖⁻¹ ∧ w ∈ Λ) := by
      intro a b w hw
      simp only [norm_one, inv_one]
      exact p1 a b w hw
    have hpos : 0 < ‖u‖ := norm_pos_iff.2 hu
    have hsp2 : ∀ (a b : L), ∀ w ∈ orthPair hh e f,
        (a • e + b • f + w ∈ Λ' ↔ ‖a‖ ≤ ‖u‖ ∧ ‖b‖ ≤ ‖u‖⁻¹ ∧ w ∈ Λ') := by
      intro a b w hw
      have key := p2 (a * u⁻¹) (b * s u) w hw
      have e1 : (a * u⁻¹) • (u • e) + (b * s u) • ((s u)⁻¹ • f) + w = a • e + b • f + w := by
        rw [smul_smul, smul_smul, mul_assoc, mul_assoc, inv_mul_cancel₀ hu,
          mul_inv_cancel₀ hsu, mul_one, mul_one]
      rw [e1] at key
      rw [key, norm_mul, norm_mul, norm_inv, hs.2.1 u, ← div_eq_mul_inv, div_le_one hpos,
        ← one_div, le_div_iff₀ hpos]
    have h1 : (fun _ : Fin (l + 1) => (1 : L)) = Fin.cons 1 (fun _ : Fin l => (1 : L)) := by
      funext i
      induction i using Fin.cases with
      | zero => rfl
      | succ i => rfl
    refine ⟨l + 1, Fin.cons e fun i => (e' i : V), Fin.cons f fun i => (f' i : V),
      W'.map (orthPair hh e f).subtype, Fin.cons u u', ?_,
      frame_cons hh hUm hee hff hef hdec hfr, ?_, adapted_cons hsp2 ad2⟩
    · intro i
      induction i using Fin.cases with
      | zero => simpa using hu
      | succ i => simpa using hu' i
    · rw [h1]
      exact adapted_cons hsp1 ad1
  · have hiso' : ∀ x, h x x = 0 → x = 0 := by
      intro x hx
      by_contra hne
      exact hiso ⟨x, hne, hx⟩
    have hm : ∀ M : AddSubgroup V, IsMax h M → ∀ x, x ∈ M ↔ ‖h x x‖ ≤ 1 :=
      fun M hM => hA L s hs δ hδ V h hh hiso' M hM
    refine ⟨0, Fin.elim0, Fin.elim0, ⊤, Fin.elim0, fun i => i.elim0,
      ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun _ _ i => i.elim0,
        fun w _ hw => hiso' w hw, fun x => ⟨Fin.elim0, Fin.elim0, x, trivial, by simp⟩⟩, ?_, ?_⟩
    · intro a b w _
      simp [hm Λ hΛ]
    · intro a b w _
      simp [hm Λ' hΛ']

theorem stFrame_of : StAniso → StPlane → StSplit → StFrame := by
  intro hA hP hS L _ _ _ _ s hs δ hδ V _ _ _ h hh
  exact exists_adapted_frame_with_unit_scaling hA hP hS L s hs δ hδ _ V h rfl hh

end GlobalTheory.CompanionTheory.HermFrame

end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FrameOfAnisotropicPlaneSplittingStatement
open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_of_anisotropic_plane_splitting : StAniso → StPlane → StSplit → StFrame := by
  first | exact @GlobalTheory.CompanionTheory.HermFrame.stFrame_of | exact GlobalTheory.CompanionTheory.HermFrame.stFrame_of | (intros; apply GlobalTheory.CompanionTheory.HermFrame.stFrame_of <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SandwichStatement
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SandwichStatement
noncomputable section

namespace GlobalTheory.CompanionTheory.Lattice

open CompanionTheory.Rg.FlB
open scoped NormedField Valued

theorem exists_common_denom {L ι : Type} [Field L] (O : Subring L)
    (hfrac : ∀ x : L, ∃ a : O, (a : L) ≠ 0 ∧ (a : L) * x ∈ O) (s : Finset ι) (g : ι → L) :
    ∃ d : O, (d : L) ≠ 0 ∧ ∀ i ∈ s, (d : L) * g i ∈ O := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by simp, by simp⟩
  | insert i s _ ih =>
    obtain ⟨d, hd, h⟩ := ih
    obtain ⟨a, ha, hi⟩ := hfrac (g i)
    refine ⟨a * d, by simp [ha, hd], fun j hj => ?_⟩
    rcases Finset.mem_insert.1 hj with rfl | hj
    · have : ((a * d : O) : L) * g j = (d : L) * ((a : L) * g j) := by push_cast; ring
      rw [this]
      exact O.mul_mem d.2 hi
    · have : ((a * d : O) : L) * g j = (a : L) * ((d : L) * g j) := by push_cast; ring
      rw [this]
      exact O.mul_mem a.2 (h j hj)

theorem exists_basis_of_pid {L V : Type} [Field L] [AddCommGroup V] [Module L V] (O : Subring L)
    [IsPrincipalIdealRing O]
    (hfrac : ∀ x : L, ∃ a : O, (a : L) ≠ 0 ∧ (a : L) * x ∈ O) {m : ℕ}
    (b : Module.Basis (Fin m) L V) (Λ : AddSubgroup V) (c : L) (hc : c ≠ 0)
    (h1 : ∀ x ∈ Λ, ∀ i, b.repr (c • x) i ∈ O) (hspan : ∀ x : V, ∃ a : L, a ≠ 0 ∧ a • x ∈ Λ)
    (hO : ∀ a ∈ O, ∀ x ∈ Λ, a • x ∈ Λ) :
    ∃ (n : ℕ) (B : Module.Basis (Fin n) L V), ∀ x, x ∈ Λ ↔ ∀ i, B.repr x i ∈ O := by
  classical

  let ψ : (Fin m → O) →ₗ[O] V :=
    { toFun := fun y => c⁻¹ • ∑ j, (y j : L) • b j
      map_add' := fun y z => by
        simp only [Pi.add_apply, Subring.coe_add, add_smul, Finset.sum_add_distrib, smul_add]
      map_smul' := fun a y => by
        simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul, RingHom.id_apply, Finset.smul_sum,
          Subring.coe_mul, mul_smul]
        exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _ }
  have hψ : ∀ y, ψ y = c⁻¹ • ∑ j, (y j : L) • b j := fun _ => rfl
  have hinj : LinearMap.ker ψ = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun y hy => ?_
    rw [hψ] at hy
    have h0 : ∑ j, (y j : L) • b j = 0 := (smul_eq_zero.1 hy).resolve_left (inv_ne_zero hc)
    have := Fintype.linearIndependent_iff.1 b.linearIndependent (fun j => (y j : L)) h0
    exact funext fun j => Subtype.ext (this j)
  let N : Submodule O (Fin m → O) :=
    { carrier := {y | ψ y ∈ Λ}
      add_mem' := fun {y z} hy hz => by
        simpa [map_add (f := _)] using Λ.add_mem hy hz
      zero_mem' := by simp [Λ.zero_mem]
      smul_mem' := fun a y hy => by
        simpa [map_smul, Subring.smul_def] using hO a a.2 _ hy }
  obtain ⟨n, bN⟩ := Submodule.basisOfPid (Pi.basisFun O (Fin m)) N
  let v : Fin n → V := fun i => ψ (bN i : Fin m → O)
  have hvΛ : ∀ i, v i ∈ Λ := fun i => (bN i).2

  have hrep : ∀ z ∈ Λ, ∃ o : Fin n → O, z = ∑ i, (o i : L) • v i := by
    intro z hz
    let y : Fin m → O := fun j => ⟨b.repr (c • z) j, h1 z hz j⟩
    have hy : ψ y = z := by
      rw [hψ]
      have : ∑ j, (y j : L) • b j = c • z := b.sum_repr (c • z)
      rw [this, smul_smul, inv_mul_cancel₀ hc, one_smul]
    have hyN : y ∈ N := by
      change ψ y ∈ Λ
      rwa [hy]
    refine ⟨fun i => bN.repr ⟨y, hyN⟩ i, ?_⟩
    have h2 := congrArg (fun w : N => ψ (w : Fin m → O)) (bN.sum_repr ⟨y, hyN⟩)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, hy] at h2
    rw [← h2]
    exact Finset.sum_congr rfl fun i _ => by rw [Subring.smul_def]

  have hliO : LinearIndependent O v := by
    have h3 : LinearIndependent O (fun i => (bN i : Fin m → O)) :=
      bN.linearIndependent.map' N.subtype (Submodule.ker_subtype N)
    exact h3.map' ψ hinj
  have hli : LinearIndependent L v := by
    refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
    obtain ⟨d, hd, hdg⟩ := exists_common_denom O hfrac Finset.univ g
    have h4 : ∑ j, (⟨(d : L) * g j, hdg j (Finset.mem_univ j)⟩ : O) • v j = 0 := by
      have : ∑ j, (⟨(d : L) * g j, hdg j (Finset.mem_univ j)⟩ : O) • v j
          = (d : L) • ∑ j, g j • v j := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [Subring.smul_def, mul_smul]
      rw [this, hg, smul_zero]
    have h5 := Fintype.linearIndependent_iff.1 hliO _ h4 i
    have h6 : (d : L) * g i = 0 := congrArg Subtype.val h5
    exact (mul_eq_zero.1 h6).resolve_left hd
  have hsp : ⊤ ≤ Submodule.span L (Set.range v) := by
    intro x _
    obtain ⟨a, ha, hax⟩ := hspan x
    obtain ⟨o, ho⟩ := hrep _ hax
    have hx : x = a⁻¹ • (a • x) := by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
    rw [hx, ho]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  let B := Module.Basis.mk hli hsp
  have hB : ∀ i, B i = v i := fun i => by simp [B]
  refine ⟨n, B, fun x => ⟨fun hx i => ?_, fun hx => ?_⟩⟩
  · obtain ⟨o, ho⟩ := hrep x hx
    have h7 : x = ∑ j, (o j : L) • B j := by simpa only [hB] using ho
    have h8 : B.repr x i = (o i : L) := by
      rw [h7, B.repr_sum_self]
    rw [h8]
    exact (o i).2
  · rw [← B.sum_repr x]
    exact Λ.sum_mem fun i _ => hO _ (hx i) _ (by rw [hB]; exact hvΛ i)

theorem stSandwich : StSandwich := by
  intro L _ _ hp V _ _ Λ₀ Λ c ⟨m, b, hb⟩ hc hcΛ hspan hO
  have hmem : ∀ x : L, x ∈ 𝒪[L] ↔ ‖x‖ ≤ 1 := fun x => Valued.integer.mem_iff
  haveI : CompactSpace 𝒪[L] := by
    have hset : ((𝒪[L] : Subring L) : Set L) = Metric.closedBall 0 1 := by
      ext x
      simp [hmem]
    have hk : IsCompact ((𝒪[L] : Subring L) : Set L) := by
      rw [hset]
      exact isCompact_closedBall 0 1
    exact isCompact_iff_compactSpace.1 hk
  haveI : (Valued.v : Valuation L NNReal).IsNontrivial := by
    obtain ⟨x, hx0, hx1⟩ := NormedField.exists_norm_lt_one L
    refine (Valued.v : Valuation L NNReal).isNontrivial_iff_exists_lt_one.2 ⟨x, ?_, ?_⟩
    · simpa using hx0
    · simpa [← NNReal.coe_lt_coe] using hx1
  haveI : IsDiscreteValuationRing 𝒪[L] := Valued.integer.isDiscreteValuationRing_of_compactSpace
  have hfrac : ∀ x : L, ∃ a : 𝒪[L], (a : L) ≠ 0 ∧ (a : L) * x ∈ 𝒪[L] := by
    intro x
    by_cases hx : ‖x‖ ≤ 1
    · exact ⟨1, by simp, by simpa using (hmem x).2 hx⟩
    · have hx0 : x ≠ 0 := by
        rintro rfl
        simp at hx
      have hlt : 1 < ‖x‖ := not_le.1 hx
      refine ⟨⟨x⁻¹, (hmem _).2 ?_⟩, by simpa using hx0, ?_⟩
      · rw [norm_inv]
        exact inv_le_one_of_one_le₀ hlt.le
      · simp [hx0, one_mem]
  obtain ⟨n, B, hB⟩ := exists_basis_of_pid 𝒪[L] hfrac b Λ c hc
    (fun x hx i => (hmem _).2 ((hb _).1 (hcΛ x hx) i)) hspan
    (fun a ha x hx => hO a ((hmem a).1 ha) x hx)
  exact ⟨n, B, fun x => (hB x).trans (forall_congr' fun i => hmem _)⟩

end GlobalTheory.CompanionTheory.Lattice
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SandwichStatementStatement
open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.SandwichStatement : StSandwich := by
  first | exact @GlobalTheory.CompanionTheory.Lattice.stSandwich | exact GlobalTheory.CompanionTheory.Lattice.stSandwich | (intros; apply GlobalTheory.CompanionTheory.Lattice.stSandwich <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DeltaStatement
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DeltaStatement
open CompanionTheory.Rg.FlB

namespace GlobalTheory.CompanionTheory.RgFl

theorem exists_isDelta (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L]
    [CharZero L] (s : L →+* L) (hs : IsInv s) : ∃ δ, IsDelta s δ := by
  obtain ⟨hss, hn, -⟩ := hs
  have hcont : Continuous s := (AddMonoidHomClass.isometry_of_norm s hn).continuous
  have h2 : (2 : L) ≠ 0 := two_ne_zero
  have h2pos : 0 < ‖(2 : L)‖ := norm_pos_iff.2 h2
  have h2le : ‖(2 : L)‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (1 : L) 1
    rw [one_add_one_eq_two] at this
    simpa using this
  have htr : ∀ y : L, ‖y‖ ≤ 1 → ‖y + s y‖ ≤ 1 := fun y hy =>
    (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hy (by rw [hn]; exact hy))

  let I : Set L := {a | ∀ x : L, ‖x‖ ≤ 1 → ‖a * x + s (a * x)‖ ≤ 1}
  have h1I : (1 : L) ∈ I := fun x hx => by simpa using htr x hx
  have hclosed : IsClosed I := by
    have : I = ⋂ (x : L) (_ : ‖x‖ ≤ 1), {a : L | ‖a * x + s (a * x)‖ ≤ 1} := by
      ext a; simp [I]
    rw [this]
    refine isClosed_iInter fun x => isClosed_iInter fun _ => isClosed_le ?_ continuous_const
    have hm : Continuous fun a : L => a * x := continuous_id.mul continuous_const
    exact (hm.add (hcont.comp hm)).norm
  obtain ⟨p, hp⟩ := NormedField.exists_one_lt_norm L
  obtain ⟨N, hNdef⟩ : ∃ N : L, N = p * s p := ⟨_, rfl⟩
  have hNfix : s N = N := by rw [hNdef, map_mul, hss, mul_comm]
  have hN1 : 1 < ‖N‖ := by
    rw [hNdef, norm_mul, hn]
    nlinarith
  have hbound : ∀ a ∈ I, ‖a‖ ≤ ‖N‖ / ‖(2 : L)‖ := by
    intro a ha
    by_contra hlt
    push_neg at hlt
    have hNle : ‖N‖ ≤ ‖N‖ / ‖(2 : L)‖ := by
      rw [le_div_iff₀ h2pos]
      nlinarith [norm_nonneg N]
    have ha1 : 1 ≤ ‖a‖ := by linarith
    obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near ha1 hN1
    have a0 : a ≠ 0 := by
      rintro rfl
      simp at ha1
      linarith
    have hapos : 0 < ‖a‖ := norm_pos_iff.2 a0
    have hx : ‖N ^ k / a‖ ≤ 1 := by
      rw [norm_div, norm_pow]
      exact (div_le_one hapos).2 hk1
    have h3 := ha _ hx
    have h4 : a * (N ^ k / a) = N ^ k := by field_simp
    rw [h4, map_pow, hNfix, ← two_mul, norm_mul, norm_pow] at h3
    have h5 : ‖N‖ ^ k ≤ 1 / ‖(2 : L)‖ := by
      rw [le_div_iff₀ h2pos]
      linarith
    have h6 : ‖N‖ ^ (k + 1) ≤ ‖N‖ / ‖(2 : L)‖ := by
      rw [pow_succ, div_eq_mul_one_div ‖N‖, mul_comm]
      exact mul_le_mul_of_nonneg_left h5 (norm_nonneg _)
    linarith
  have hIc : IsCompact I :=
    (isCompact_closedBall (0 : L) (‖N‖ / ‖(2 : L)‖)).of_isClosed_subset hclosed
      (fun a ha => by simpa using hbound a ha)
  obtain ⟨δ, hδ, hmax⟩ := hIc.exists_isMaxOn ⟨1, h1I⟩ continuous_norm.continuousOn
  have hmax' : ∀ a ∈ I, ‖a‖ ≤ ‖δ‖ := fun a ha => hmax ha
  have hδ1 : 1 ≤ ‖δ‖ := by simpa using hmax' 1 h1I
  have δ0 : δ ≠ 0 := by
    rintro rfl
    simp at hδ1
    linarith
  have hδpos : 0 < ‖δ‖ := norm_pos_iff.2 δ0

  have hf : Continuous fun x : L => ‖x * δ + s (x * δ)‖ := by
    have hm : Continuous fun a : L => a * δ := continuous_id.mul continuous_const
    exact (hm.add (hcont.comp hm)).norm
  obtain ⟨x₀, hx₀, hx₀max⟩ := (isCompact_closedBall (0 : L) 1).exists_isMaxOn
    ⟨0, by simp⟩ hf.continuousOn
  have hx₀' : ‖x₀‖ ≤ 1 := by simpa using hx₀
  have hfmax : ∀ x : L, ‖x‖ ≤ 1 → ‖x * δ + s (x * δ)‖ ≤ ‖x₀ * δ + s (x₀ * δ)‖ := fun x hx =>
    hx₀max (by simpa using hx)
  obtain ⟨m, hm⟩ : ∃ m : L, m = x₀ * δ + s (x₀ * δ) := ⟨_, rfl⟩
  rw [← hm] at hfmax
  have hmfix : s m = m := by rw [hm, map_add (f := _), hss, add_comm]
  have hm1 : ‖m‖ ≤ 1 := by
    rw [hm, mul_comm]
    exact hδ x₀ hx₀'
  have hm0 : m ≠ 0 := by
    have hx : ‖δ⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ hδ1
    have h3 := hfmax _ hx
    have h4 : δ⁻¹ * δ = 1 := inv_mul_cancel₀ δ0
    rw [h4, map_one, one_add_one_eq_two] at h3
    intro h
    rw [h, norm_zero] at h3
    linarith
  have hmpos : 0 < ‖m‖ := norm_pos_iff.2 hm0
  have hmeq : ‖m‖ = 1 := by
    by_contra hne
    have hlt : ‖m‖ < 1 := lt_of_le_of_ne hm1 hne
    have hI' : δ / m ∈ I := by
      intro x hx
      have h3 : δ / m * x + s (δ / m * x) = (x * δ + s (x * δ)) / m := by
        rw [map_mul, map_div₀, hmfix, map_mul]
        field_simp
      rw [h3, norm_div]
      exact (div_le_one hmpos).2 (hfmax x hx)
    have h4 := hmax' _ hI'
    rw [norm_div, div_le_iff₀ hmpos] at h4
    nlinarith
  refine ⟨δ, δ0, fun a => ⟨fun ha => hmax' a ha, fun ha x hx => ?_⟩, x₀ / m, ?_, ?_⟩
  · have h3 : a * x = δ * (a / δ * x) := by field_simp
    rw [h3]
    refine hδ _ ?_
    rw [norm_mul, norm_div]
    exact mul_le_one₀ ((div_le_one hδpos).2 ha) (norm_nonneg _) hx
  · rw [norm_div, hmeq, div_one]
    exact hx₀'
  · have h3 : x₀ / m * δ + s (x₀ / m * δ) = (x₀ * δ + s (x₀ * δ)) / m := by
      rw [map_mul, map_div₀, hmfix, map_mul]
      field_simp
    rw [h3, ← hm, div_self hm0]

theorem stDelta : StDelta := fun L _ _ _ _ s hs => exists_isDelta L s hs

end GlobalTheory.CompanionTheory.RgFl
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DeltaStatementStatement
open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.DeltaStatement : StDelta := by
  first | exact @GlobalTheory.CompanionTheory.RgFl.stDelta | exact GlobalTheory.CompanionTheory.RgFl.stDelta | (intros; apply GlobalTheory.CompanionTheory.RgFl.stDelta <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistenceOfSandwichStatement
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistenceOfSandwichStatement
open CompanionTheory.Rg.FlB

noncomputable section

namespace GlobalTheory.CompanionTheory.RgFl.MaxLat

variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L]
  {V : Type} [AddCommGroup V] [Module L V]

theorem herm_add_left {s : L →+* L} {h : V → V → L} (hh : IsHerm s h) (x y z : V) :
    h (x + y) z = h x z + h y z := by
  rw [hh.2.2.1 z (x + y), hh.1, map_add (f := _), ← hh.2.2.1 z x, ← hh.2.2.1 z y]

def hLin {s : L →+* L} {h : V → V → L} (hh : IsHerm s h) (z : V) : V →ₗ[L] L where
  toFun := h z
  map_add' := hh.1 z
  map_smul' a y := by simpa using hh.2.1 a z y

theorem herm_eq_sum {s : L →+* L} {h : V → V → L} (hh : IsHerm s h) {ι : Type} [Fintype ι]
    (b : Module.Basis ι L V) (z y : V) : h z y = ∑ j, b.repr y j * h z (b j) := by
  calc h z y = hLin hh z y := rfl
    _ = hLin hh z (∑ j, b.repr y j • b j) := by rw [b.sum_repr]
    _ = ∑ j, b.repr y j * h z (b j) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul]
      rfl

theorem norm_sub_le_max_of_ultrametric_field (a b : L) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  simpa [sub_eq_add_neg] using IsUltrametricDist.norm_add_le_max a (-b)

theorem norm_herm_le_delta {s : L →+* L} {δ : L} {h : V → V → L} (hδ : IsDelta s δ)
    (hh : IsHerm s h) {M : AddSubgroup V} (hO : ∀ a : L, ‖a‖ ≤ 1 → ∀ x ∈ M, a • x ∈ M)
    (hM : ∀ x ∈ M, ‖h x x‖ ≤ 1) {x y : V} (hx : x ∈ M) (hy : y ∈ M) : ‖h x y‖ ≤ ‖δ‖ := by
  refine (hδ.2.1 (h x y)).1 fun t ht => ?_
  have hy' : t • y ∈ M := hO t ht y hy
  have e1 : h x (t • y) = h x y * t := by rw [hh.2.1, mul_comm]
  have e2 : h (t • y) x = s (h x y * t) := by rw [hh.2.2.1 x (t • y), e1]
  have e3 : h (x + t • y) (x + t • y)
      = h x x + (h x y * t + s (h x y * t)) + h (t • y) (t • y) := by
    rw [herm_add_left hh, hh.1, hh.1, e1, e2]; ring
  have e4 : h x y * t + s (h x y * t)
      = h (x + t • y) (x + t • y) - h x x - h (t • y) (t • y) := by
    rw [e3]; ring
  rw [e4]
  exact (norm_sub_le_max_of_ultrametric_field _ _).trans (max_le
    ((norm_sub_le_max_of_ultrametric_field _ _).trans
      (max_le (hM _ (M.add_mem hx hy')) (hM _ hx))) (hM _ hy'))

theorem exists_basis_herm_le_one [FiniteDimensional L V] {s : L →+* L} {h : V → V → L}
    (hs : IsInv s) (hh : IsHerm s h) :
    ∃ (m : ℕ) (b : Module.Basis (Fin m) L V), ∀ i j, ‖h (b i) (b j)‖ ≤ 1 := by
  let e := Module.finBasis L V
  let K : ℝ := ∑ i, ∑ j, ‖h (e i) (e j)‖
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hKij : ∀ i j, ‖h (e i) (e j)‖ ≤ K := fun i j =>
    (Finset.single_le_sum (f := fun j => ‖h (e i) (e j)‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, ‖h (e i) (e j)‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))
  obtain ⟨t, ht0, ht⟩ := NormedField.exists_norm_lt L (show (0 : ℝ) < 1 / (K + 1) by positivity)
  have htK : ‖t‖ * (K + 1) ≤ 1 := by
    rw [lt_div_iff₀ (by positivity)] at ht
    exact ht.le
  have ht1 : ‖t‖ ≤ 1 := by nlinarith [norm_nonneg t]
  have htK' : ‖t‖ * K ≤ 1 := by nlinarith [norm_nonneg t]
  have tne : t ≠ 0 := norm_pos_iff.1 ht0
  have hu : ∀ i : Fin (Module.finrank L V), IsUnit ((fun _ => t) i : L) :=
    fun _ => isUnit_iff_ne_zero.2 tne
  refine ⟨_, e.isUnitSMul hu, fun i j => ?_⟩
  simp only [Module.Basis.isUnitSMul_apply]
  have e1 : h (t • e i) (t • e j) = t * (s t * h (e i) (e j)) := by
    rw [hh.2.1, hh.2.2.1 (e j) (t • e i), hh.2.1, map_mul, ← hh.2.2.1 (e j) (e i)]
  rw [e1, norm_mul, norm_mul, hs.2.1]
  calc ‖t‖ * (‖t‖ * ‖h (e i) (e j)‖) ≤ 1 * (‖t‖ * K) := by
        gcongr
        exact hKij i j
    _ ≤ 1 := by linarith

def ball {ι : Type} (b : Module.Basis ι L V) : AddSubgroup V where
  carrier := {x | ∀ i, ‖b.repr x i‖ ≤ 1}
  add_mem' {x y} hx hy i := by
    simpa using (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx i) (hy i))
  zero_mem' i := by simp
  neg_mem' {x} hx i := by simpa using hx i

theorem basis_mem_ball {ι : Type} [DecidableEq ι] (b : Module.Basis ι L V) (j : ι) :
    b j ∈ ball b := by
  intro i
  rw [b.repr_self, Finsupp.single_apply]
  split_ifs <;> simp

theorem IsLat.smul_mem {Λ : AddSubgroup V} (hΛ : IsLat L Λ) {a : L} (ha : ‖a‖ ≤ 1) {x : V}
    (hx : x ∈ Λ) : a • x ∈ Λ := by
  obtain ⟨m, b, hb⟩ := hΛ
  rw [hb] at hx ⊢
  intro i
  simpa using mul_le_one₀ ha (norm_nonneg _) (hx i)

theorem ball_absorbing {m : ℕ} (b : Module.Basis (Fin m) L V) (x : V) :
    ∃ a : L, a ≠ 0 ∧ a • x ∈ ball b := by
  let K : ℝ := ∑ i, ‖b.repr x i‖
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ => norm_nonneg _
  obtain ⟨t, ht0, ht⟩ := NormedField.exists_norm_lt L (show (0 : ℝ) < 1 / (K + 1) by positivity)
  have htK : ‖t‖ * (K + 1) ≤ 1 := by
    rw [lt_div_iff₀ (by positivity)] at ht
    exact ht.le
  refine ⟨t, norm_pos_iff.1 ht0, fun i => ?_⟩
  have hi : ‖b.repr x i‖ ≤ K :=
    Finset.single_le_sum (f := fun i => ‖b.repr x i‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul]
  nlinarith [norm_nonneg t, norm_nonneg (b.repr x i)]

theorem norm_herm_ball_le_one {s : L →+* L} {h : V → V → L} (hs : IsInv s) (hh : IsHerm s h)
    {m : ℕ} (b : Module.Basis (Fin m) L V) (hb : ∀ i j, ‖h (b i) (b j)‖ ≤ 1) {x : V}
    (hx : x ∈ ball b) : ‖h x x‖ ≤ 1 := by
  have h1 : ∀ j, ‖h (b j) x‖ ≤ 1 := fun j => by
    rw [herm_eq_sum hh b]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (hx i) (norm_nonneg _) (hb j i)
  rw [herm_eq_sum hh b]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun j _ => ?_
  rw [norm_mul, hh.2.2.1 (b j) x, hs.2.1]
  exact mul_le_one₀ (hx j) (norm_nonneg _) (h1 j)

theorem exists_scale {s : L →+* L} {h : V → V → L} (hh : IsHerm s h) (B : ℝ) (hB : 0 ≤ B)
    {m : ℕ} (b : Module.Basis (Fin m) L V) :
    ∃ c : L, c ≠ 0 ∧ ∀ x, (∀ j, ‖h (b j) x‖ ≤ B) → c • x ∈ ball b := by
  let T : V →ₗ[L] (Fin m → L) := LinearMap.pi fun j => hLin hh (b j)
  have hT : LinearMap.ker T = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun x hx => hh.2.2.2 x fun y => ?_
    have hj : ∀ j, h (b j) x = 0 := fun j => congrFun hx j
    rw [herm_eq_sum hh b]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [hh.2.2.1 (b j) x, hj j, map_zero, mul_zero]
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective T hT
  let w : Fin m → V := fun k => g fun j => if k = j then 1 else 0
  have hx : ∀ x, x = ∑ k, h (b k) x • w k := fun x => by
    have h1 : g (T x) = x := by simpa using LinearMap.congr_fun hg x
    have h2 := LinearMap.pi_apply_eq_sum_univ g (T x)
    rw [h1] at h2
    exact h2
  let C : ℝ := ∑ k, ∑ i, ‖b.repr (w k) i‖
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hCki : ∀ k i, ‖b.repr (w k) i‖ ≤ C := fun k i =>
    (Finset.single_le_sum (f := fun i => ‖b.repr (w k) i‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ i)).trans
      (Finset.single_le_sum (f := fun k => ∑ i, ‖b.repr (w k) i‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ k))
  obtain ⟨c, hc0, hc⟩ :=
    NormedField.exists_norm_lt L (show (0 : ℝ) < 1 / (B * C + 1) by positivity)
  have hcK : ‖c‖ * (B * C + 1) ≤ 1 := by
    rw [lt_div_iff₀ (by positivity)] at hc
    exact hc.le
  refine ⟨c, norm_pos_iff.1 hc0, fun x hxB i => ?_⟩
  have hr : b.repr x i = ∑ k, h (b k) x * b.repr (w k) i := by
    conv_lhs => rw [hx x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, Finsupp.finsetSum_apply]
  have hbound : ‖b.repr x i‖ ≤ B * C := by
    rw [hr]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun k _ => ?_
    rw [norm_mul]
    exact mul_le_mul (hxB k) (hCki k i) (norm_nonneg _) hB
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul]
  nlinarith [norm_nonneg c, norm_nonneg (b.repr x i)]

theorem stExists_of_stSandwich : StSandwich → StExists := by
  intro hSw
  unfold StExists ForAll
  intro L _ _ _ _ s hs δ hδ V _ _ _ h hh
  obtain ⟨m, b, hb⟩ := exists_basis_herm_le_one hs hh
  obtain ⟨c, hc0, hc⟩ := exists_scale hh ‖δ‖ (norm_nonneg _) b
  let S : Set (AddSubgroup V) :=
    {Λ | (∀ a : L, ‖a‖ ≤ 1 → ∀ x ∈ Λ, a • x ∈ Λ) ∧ ∀ x ∈ Λ, ‖h x x‖ ≤ 1}
  have hlat0 : IsLat L (ball b) := ⟨m, b, fun _ => Iff.rfl⟩
  have hS0 : ball b ∈ S :=
    ⟨fun a ha x hx => IsLat.smul_mem hlat0 ha hx, fun x hx => norm_herm_ball_le_one hs hh b hb hx⟩
  have hchain : ∀ C ⊆ S, IsChain (· ≤ ·) C → ∀ y ∈ C, ∃ ub ∈ S, ∀ z ∈ C, z ≤ ub := by
    intro C hCS hC y hy
    have hmem : ∀ x, x ∈ sSup C ↔ ∃ t ∈ C, x ∈ t := fun x =>
      AddSubgroup.mem_sSup_of_directedOn ⟨y, hy⟩ hC.directedOn
    refine ⟨sSup C, ⟨fun a ha x hx => ?_, fun x hx => ?_⟩, fun z hz => le_sSup hz⟩
    · obtain ⟨t, ht, hxt⟩ := (hmem x).1 hx
      exact (hmem _).2 ⟨t, ht, (hCS ht).1 a ha x hxt⟩
    · obtain ⟨t, ht, hxt⟩ := (hmem x).1 hx
      exact (hCS ht).2 x hxt
  obtain ⟨M, hM0, hMax⟩ := zorn_le_nonempty₀ S hchain (ball b) hS0
  have hMlat : IsLat L M := by
    refine hSw L V (ball b) M c hlat0 hc0 (fun x hx => hc x fun j => ?_) (fun x => ?_) hMax.prop.1
    · exact norm_herm_le_delta hδ hh hMax.prop.1 hMax.prop.2 (hM0 (basis_mem_ball b j)) hx
    · obtain ⟨a, ha, hax⟩ := ball_absorbing b x
      exact ⟨a, ha, hM0 hax⟩
  refine ⟨M, hMlat, hMax.prop.2, fun Λ' hL hI hle => ?_⟩
  exact le_antisymm (hMax.2 ⟨fun a ha x hx => IsLat.smul_mem hL ha hx, hI⟩ hle) hle

end GlobalTheory.CompanionTheory.RgFl.MaxLat

end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistenceOfSandwichStatementStatement
open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existence_of_sandwich_statement : StSandwich → StExists := by
  first | exact @GlobalTheory.CompanionTheory.RgFl.MaxLat.stExists_of_stSandwich | exact GlobalTheory.CompanionTheory.RgFl.MaxLat.stExists_of_stSandwich | (intros; apply GlobalTheory.CompanionTheory.RgFl.MaxLat.stExists_of_stSandwich <;> assumption)
end
end

section -- merged from CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.AdmissibleOf
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AdelicU GlobalTheory.AutMult
open GlobalTheory.PRep (fixed)

namespace CompanionTheory.Rg.Fl

def LocPI : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F))
      (U : Subgroup (GLoc σ J v)), IsOpen (U : Set (GLoc σ J v)) → ∃ K ≤ U, ∃ M, HasPI K M

theorem locPI_of (h2 : StSimple) (h3 : StStar) (h4 : StHecke) (h5 : StMod) (h7 : StTransfer) (hP : StPair)
    (hU : StCartanU) (hG : StCartanGL) (hM : StMove) (hD : StDict) (hC1 : StDefinite) (hC2 : StSepDef)
    (hC3 : StSepMove) : LocPI := by
  intro F E _ _ _ _ _ σ hc n J hJ v U hUo
  have hcar : HasCartan (GLoc σ J v) := by
    obtain ⟨L, _, _, _, _, h⟩ := hD F E σ hc n J hJ v
    rcases h with ⟨⟨e⟩⟩ | ⟨s, J', a1, a2, a3, a4, a5, ⟨e⟩⟩
    · exact hM _ _ e (hG L n)
    · exact hM _ _ e (hU L s a1 a2 a3 n J' a4 a5)
  obtain ⟨K, hKU, ho, hk, d, l, hcl⟩ := hcar U hUo
  obtain ⟨J', hJ', hpos, ⟨e⟩⟩ := hC1 F E σ hc n J hJ v
  have hco : ((K.map e.toMulEquiv.toMonoidHom : Subgroup _) : Set (GLoc σ J' v)) = e '' K := Subgroup.coe_map _ _
  exact ⟨K, hKU, hasPI_of h2 h3 h4 h5 h7 (hP _ K ho hk) hcl (hC3 _ _ e.toMulEquiv K
    (hC2 F E σ hc n J' hJ' hpos v _ (hco ▸ e.toHomeomorph.isOpenMap _ ho) (hco ▸ hk.image e.continuous)))⟩

theorem admissible_of (hL : LocPI) (hP : StProj) : GlobalTheory.Published.UnitaryIrreducibleAdmissible := by
  intro F E _ _ _ _ _ σ hc n J hJ v H _ _ π hπ U ho _
  haveI := hπ.complete
  obtain ⟨K, hKU, M, hM⟩ := hL F E σ hc n J hJ v U ho
  obtain ⟨P, hP1, -⟩ := hP _ H π hπ.unitary.norm_apply K
  have hfin := (CompanionTheory.D.gk.admitted.finite_rank_of_irreducible_unitary _ H π hπ.unitary.norm_apply (fun S hS h => hπ.irred.2 S ⟨hS, h⟩) P M
    (hM H π hπ.unitary.norm_apply P hP1)).1
  refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range (P : H →ₗ[ℂ] H)) fun x hx => ⟨x, ?_⟩
  exact hP1.2.1 x fun k hk => GlobalTheory.LGrp.mem_fixed.1 hx k (hKU hk)

theorem flath_of (hL : LocPI) (hP : StProj) (hV : StFixVec) (hF : StFactor) (hA : StArchPI) (hI : StIso) (hO : StOp)
    (hT : StTensor) : GlobalTheory.Published.FlathTensorProduct := by
  intro F E _ _ _ _ _ σ hc n J hJ H _ _ π hπ
  haveI := hπ.complete
  haveI := hπ.irred.1
  have hcomm : ∀ v x g, projPl σ J v g = 1 → Commute (embPl σ J v x) g := by
    rintro (w | v) x g hg
    · exact commute_embArch σ J x hg
    · exact commute_emb σ J x hg
  have hu : ∀ v, IsUnitaryRep (π.comp (embPl σ J v)) := fun v => isUnitaryRep_comp hπ.unitary (continuous_embPl σ J v)
  have hproj : ∀ v, ∃ P, IsPIProj (π.comp (embPl σ J v)) P := by
    rintro (w | v)
    · exact hA F E σ hc n J hJ w H _ (hu (.inl w))
    · haveI := GlobalTheory.Doubling.nonarchimedeanGroup_GLoc σ J v
      have h1 : IsUnitaryRep (π.comp (emb σ J v)) := hu (.inr v)
      obtain ⟨U, x, ho, hx, hfix⟩ := hV _ H _ h1.norm_apply h1.continuous_apply
      obtain ⟨K, hKU, M, hM⟩ := hL F E σ hc n J hJ v U ho
      obtain ⟨P, hP1, hP2, hP3⟩ := hP _ H _ h1.norm_apply K
      refine ⟨P, fun h0 => hx ?_, ContinuousLinearMap.ext fun y => hP1.2.1 _ (hP1.1 y), hP2, hP3, M,
        hM H _ h1.norm_apply P hP1⟩
      rw [← hP1.2.1 x fun k hk => hfix k (hKU hk), h0]; rfl
  have hR : ∀ v, ∃ δ : IrrU (GPl σ J v), HasCompPl σ J v δ.π π := fun v => by
    obtain ⟨P, hP'⟩ := hproj v
    obtain ⟨W, hW⟩ := hF _ _ H π hπ.unitary.norm_apply hπ.irred _ _ (projPl_embPl_self σ J v) (hcomm v) P hP'
    exact hI _ _ H π hπ _ _ (continuous_embPl σ J v) (projPl_embPl_self σ J v) (hcomm v) W hW
  choose R hR using hR
  obtain ⟨ξ, B, h⟩ := hT hO hV (admissible_of hL hP) F E σ hc n J hJ H π hπ R hR
  exact ⟨R, ξ, B, h⟩

end CompanionTheory.Rg.Fl

end
end

namespace CompanionTheory.Rg.Fl.B

theorem stFrame : CompanionTheory.Rg.FlB.StFrame :=
  GlobalTheory.T.frame_of_anisotropic_plane_splitting (GlobalTheory.T.anisotropic_of_hensel_and_sandwich GlobalTheory.T.HenselStatement GlobalTheory.T.SandwichStatement) (GlobalTheory.T.plane_of_hensel_and_pairing GlobalTheory.T.HenselStatement (GlobalTheory.T.pairing_of_sandwich_statement GlobalTheory.T.SandwichStatement))
    (GlobalTheory.T.splitting_of_sandwich_and_pairing GlobalTheory.T.SandwichStatement (GlobalTheory.T.pairing_of_sandwich_statement GlobalTheory.T.SandwichStatement))

theorem stCartanU : StCartanU :=
  GlobalTheory.T.isometric_lattice_congruence_subgroups GlobalTheory.T.DeltaStatement (GlobalTheory.T.existence_of_sandwich_statement GlobalTheory.T.SandwichStatement) stFrame GlobalTheory.T.TorusStatement (GlobalTheory.T.decomposition_of_frame_witt_torus stFrame GlobalTheory.T.WittStatement GlobalTheory.T.TorusStatement)
    GlobalTheory.T.IwahoriStatement GlobalTheory.T.lattice_congruence_subgroups_open_compact

theorem locPI : LocPI :=
  locPI_of (GlobalTheory.T.simple_of_commutative_statement GlobalTheory.T.StatementCommutative) GlobalTheory.T.StatementStar GlobalTheory.T.HeckeAlgebraTheorem GlobalTheory.T.ModularityStatement GlobalTheory.T.TransferStatementBis GlobalTheory.T.PairingStatement stCartanU GlobalTheory.T.CartanDecompositionGL
    GlobalTheory.T.MovingStatement GlobalTheory.T.DictionaryStatement GlobalTheory.T.DefinitenessStatement CompanionTheory.Rg.FlSep.stSepDefB GlobalTheory.T.SeparatedMovingStatement

theorem unitaryIrreducibleAdmissible : GlobalTheory.Published.UnitaryIrreducibleAdmissible := admissible_of locPI GlobalTheory.T.ProjectionStatement

theorem flathTensorProduct : GlobalTheory.Published.FlathTensorProduct :=
  flath_of locPI GlobalTheory.T.ProjectionStatement GlobalTheory.T.FixedVectorStatement GlobalTheory.T.FactorizationStatement GlobalTheory.T.ArchimedeanPrincipalSeries GlobalTheory.T.IsomorphismStatement GlobalTheory.T.OperatorStatement GlobalTheory.T.stTensor'

end CompanionTheory.Rg.Fl.B
