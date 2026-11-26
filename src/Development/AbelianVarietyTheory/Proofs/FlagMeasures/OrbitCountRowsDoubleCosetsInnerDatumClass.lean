module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticeAutomorphismsEqAdaptedModUnipotent
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardStabilizerInnerDatumRowDoubleCoset
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermRepUnram

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsTermTranslateByAdaptedLatticeAutomorphisms
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvUnitriangularMoveFrameMemFlagSubspace
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvUnitriangularMoveFrameMemFlagSubspace
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat IsDedekindDomain

namespace GlobalTheory.FlagInv

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem map_Xflag_le (F : LFlag S r T) (a : S.V ≃ₗ[E] S.V)
    (h : ∀ b : Fin (r + 1), a (frame F b) - frame F b ∈ Xflag F b.val) (j : ℕ) :
    (Xflag F j).map (a : S.V →ₗ[E] S.V) ≤ Xflag F j := by
  show (F.fl.Xa j).map (a : S.V →ₗ[E] S.V) ≤ F.fl.Xa j
  rw [Submodule.map_le_iff_le_comap]
  unfold Formalism.MainNotions.S.FlagG.Xa
  rw [Submodule.span_le]
  rintro _ ⟨i, hi, rfl⟩
  simp only [Set.mem_setOf_eq] at hi
  simp only [SetLike.mem_coe, Submodule.mem_comap, LinearEquiv.coe_coe]
  have hb := h (Fin.castSucc i)
  have hf : frame F (Fin.castSucc i) = F.fl.e i := by
    simp [frame, Formalism.MainNotions.S.FlagG.fvec]
  rw [hf] at hb
  have hmono : Xflag F (Fin.castSucc i).val ≤ F.fl.Xa j := by
    show F.fl.Xa i.val ≤ F.fl.Xa j
    unfold Formalism.MainNotions.S.FlagG.Xa
    apply Submodule.span_mono
    apply Set.image_mono
    intro k hk
    simp only [Set.mem_setOf_eq] at hk ⊢
    omega
  have he : F.fl.e i ∈ F.fl.Xa j := by
    unfold Formalism.MainNotions.S.FlagG.Xa
    exact Submodule.subset_span ⟨i, hi, rfl⟩
  have := Submodule.add_mem _ (hmono hb) he
  unfold Formalism.MainNotions.S.FlagG.Xa at this
  simpa using this

theorem map_Xflag_eq (F : LFlag S r T) (a : S.V ≃ₗ[E] S.V)
    (h : ∀ b : Fin (r + 1), a (frame F b) - frame F b ∈ Xflag F b.val) (j : ℕ) :
    (Xflag F j).map (a : S.V →ₗ[E] S.V) = Xflag F j := by
  haveI : FiniteDimensional E (Xflag F j) := by
    show FiniteDimensional E (Submodule.span E (F.fl.e '' {i | i.1 < j}))
    exact FiniteDimensional.span_of_finite E (Set.toFinite _)
  exact Submodule.eq_of_le_of_finrank_eq (map_Xflag_le F a h j) (LinearEquiv.finrank_map_eq a _)

theorem symm_mem_Xflag (F : LFlag S r T) (a : S.V ≃ₗ[E] S.V)
    (h : ∀ b : Fin (r + 1), a (frame F b) - frame F b ∈ Xflag F b.val) (j : ℕ) {x : S.V}
    (hx : x ∈ Xflag F j) : a.symm x ∈ Xflag F j := by
  rw [← map_Xflag_eq F a h j] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  simpa using hy

theorem inv_moves : ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : StarRing E] {S : HSpace E} {r : ℕ} {T : E} (F : LFlag S r T) (a : S.V ≃ₗ[E] S.V), (∀ b : Fin (r + 1), a (frame F b) - frame F b ∈ Xflag F b.val) → ∀ b : Fin (r + 1), a⁻¹ (frame F b) - frame F b ∈ Xflag F b.val := by
  intro E _ _ _ S r T F a h b
  have hm := symm_mem_Xflag F a h b.val (h b)
  have key : a⁻¹ (frame F b) - frame F b = -(a.symm (a (frame F b) - frame F b)) := by
    show a.symm (frame F b) - frame F b = _
    simp [map_sub]
  rw [key]
  exact Submodule.neg_mem _ hm

end GlobalTheory.FlagInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvUnitriangularMoveFrameMemFlagSubspaceStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inv_unitriangular_move_frame_mem_flagSubspace : ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : StarRing E] {S : HSpace E} {r : ℕ} {T : E} (F : LFlag S r T) (a : S.V ≃ₗ[E] S.V), (∀ b : Fin (r + 1), a (frame F b) - frame F b ∈ Xflag F b.val) → ∀ b : Fin (r + 1), a⁻¹ (frame F b) - frame F b ∈ Xflag F b.val := by
  first | exact @GlobalTheory.FlagInv.inv_moves | exact GlobalTheory.FlagInv.inv_moves | (intros; apply GlobalTheory.FlagInv.inv_moves <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagCoefIntegralOfLocalIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagCoefIntegralOfLocalIntegral
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat IsDedekindDomain

namespace GlobalTheory.FlagCoef

theorem coef_integral_of_flag {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
    (Λ : Submodule (𝓞 E) S.V) (g : ℕ) {T : E} (F : LFlag S r T) (hc : IsFixedConv Λ g F)
    (j : ℕ) (x : S.V) (hx : x ∈ Xflag F j)
    (hP : ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal →
      x ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ)) :
    ∃ w : Fin r → E, x = ∑ c, w c • F.fl.e c ∧ (∀ c : Fin r, j ≤ c.val → w c = 0) ∧
      ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∀ c, ∃ s : 𝓞 E, s ∉ P.asIdeal ∧
        ∃ o : 𝓞 E, (s : E) * w c = o := by
  classical
  have hxa : x ∈ Submodule.span E (F.fl.e '' {i | i.1 < j}) := hx
  obtain ⟨l, hl, hlx⟩ := (Finsupp.mem_span_image_iff_linearCombination E).1 hxa

  have hxw : x = ∑ i, l i • F.fl.e i := by
    rw [← hlx, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    intro i
    simp
  refine ⟨fun c => l c, hxw, ?_, ?_⟩
  · intro c hc
    by_contra h
    have hmem : c.val < j := hl (Finsupp.mem_support_iff.2 h)
    omega
  · intro P hgP c
    have := P.isPrime
    have key : ∀ {L : Submodule (𝓞 E) S.V} {y : S.V},
        y ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal L ↔ ∃ u ∈ P.asIdeal.primeCompl, u • y ∈ L := Iff.rfl

    obtain ⟨s, hs, hsx⟩ := key.1 (hP P hgP)
    have hxX : x ∈ Submodule.span E (Set.range F.fl.e) :=
      Submodule.span_mono (Set.image_subset_range _ _) hxa
    have hsX : s • x ∈ Formalism.MainNotions.S.Lat.XLam Λ F := by
      refine Submodule.mem_inf.2 ⟨hsx, ?_⟩
      exact Submodule.smul_of_tower_mem _ s hxX

    obtain ⟨cc, -, hc1, heq⟩ := hc.1 P
    have hloc : s • x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.MainNotions.S.Lat.XLam Λ F) :=
      key.2 ⟨1, P.asIdeal.primeCompl.one_mem, by rw [one_smul]; exact hsX⟩
    have hfun : (fun a => cc a • F.fl.e a) = F.fl.e :=
      funext fun a => by rw [hc1 hgP a, one_smul]
    rw [heq, hfun] at hloc
    obtain ⟨t, ht, htx⟩ := key.1 hloc
    obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 htx
    have h1 : ∑ i, ((o i : 𝓞 E) : E) • F.fl.e i = t • s • x := by
      rw [← ho]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact algebraMap_smul E (o i) (F.fl.e i)
    have h2 : t • s • x = ∑ i, (((t * s : 𝓞 E) : E) * l i) • F.fl.e i := by
      rw [← mul_smul, ← algebraMap_smul E (t * s) x, hxw, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_smul]
    have hsum : ∑ i, (((o i : 𝓞 E) : E) - ((t * s : 𝓞 E) : E) * l i) • F.fl.e i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, h1, ← h2, sub_self]
    have hc0 := Fintype.linearIndependent_iff.1 F.fl.e_indep _ hsum c
    exact ⟨t * s, P.asIdeal.primeCompl.mul_mem ht hs, o c, (sub_eq_zero.1 hc0).symm⟩

end GlobalTheory.FlagCoef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagCoefIntegralOfLocalIntegralStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_coef_integral_of_local_integral : ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : StarRing E] {S : HSpace E} {r : ℕ} (Λ : Submodule (𝓞 E) S.V) (g : ℕ) {T : E} (F : LFlag S r T), IsFixedConv Λ g F → ∀ (j : ℕ) (x : S.V), x ∈ Xflag F j → (∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → x ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ)) → ∃ w : Fin r → E, x = ∑ c, w c • F.fl.e c ∧ (∀ c : Fin r, j ≤ c.val → w c = 0) ∧ ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∀ c, ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∃ o : 𝓞 E, (s : E) * w c = o := by
  first | exact @GlobalTheory.FlagCoef.coef_integral_of_flag | exact GlobalTheory.FlagCoef.coef_integral_of_flag | (intros; apply GlobalTheory.FlagCoef.coef_integral_of_flag <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameAdmissibleOfCongrUnitriangular
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameAdmissibleOfCongrUnitriangular
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat IsDedekindDomain

namespace GlobalTheory

theorem exists_int_sub_eq_mul_of_integral_over {E : Type} [Field E] [NumberField E]
    (g : ℕ) (hg : g ≠ 0) (m : E)
    (hm : ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal →
      ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∃ o : 𝓞 E, (s : E) * m = o) :
    ∃ ξ c : 𝓞 E, m - (ξ : E) = (g : E) * (c : E) * m := by
  let D : Ideal (𝓞 E) := Submodule.comap (LinearMap.toSpanSingleton (𝓞 E) E m) 1
  have hD : ∀ s : 𝓞 E, s ∈ D ↔ ∃ o : 𝓞 E, (s : E) * m = o := by
    intro s
    simp only [D, Submodule.mem_comap, LinearMap.toSpanSingleton_apply, Submodule.mem_one]
    constructor
    · rintro ⟨y, hy⟩; exact ⟨y, by rw [Algebra.smul_def] at hy; exact hy.symm⟩
    · rintro ⟨o, ho⟩; exact ⟨o, by rw [Algebra.smul_def]; exact ho.symm⟩
  have htop : D ⊔ Ideal.span {(g : 𝓞 E)} = ⊤ := by
    by_contra hne
    obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_le_maximal _ hne
    have hgQ : (g : 𝓞 E) ∈ Q := hQ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hg0 : (g : 𝓞 E) ≠ 0 := by exact_mod_cast hg
    have hQbot : Q ≠ ⊥ := fun h => hg0 (by rw [h] at hgQ; simpa using hgQ)
    obtain ⟨s, hs, o, ho⟩ := hm ⟨Q, hQmax.isPrime, hQbot⟩ hgQ
    exact hs (hQ (Ideal.mem_sup_left ((hD s).2 ⟨o, ho⟩)))
  have h1 : (1 : 𝓞 E) ∈ D ⊔ Ideal.span {(g : 𝓞 E)} := by rw [htop]; trivial
  obtain ⟨d, hd, y, hy, hdy⟩ := Submodule.mem_sup.1 h1
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  obtain ⟨o, ho⟩ := (hD d).1 hd
  refine ⟨o, c, ?_⟩
  have e := congrArg (fun x : 𝓞 E => (x : E)) hdy
  push_cast at e
  rw [← ho]
  linear_combination (-m) * e

theorem admissible_of_congr_unitriangular {E : Type} [Field E] [NumberField E] [StarRing E]
    {S : HSpace E} {r : ℕ} (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (hg : g ≠ 0) {T T' : E}
    (F : LFlag S r T) (F' : LFlag S r T') (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hlow : ∀ a b, b < a → M a b = 0) (hdiag : ∀ a, M a a = 1)
    (hint : ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∀ a b,
      ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∃ o : 𝓞 E, (s : E) * M a b = o)
    (hloc : ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∀ a,
      frame F a ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ))
    (hmod : ∀ b, ModG S Λ g (frame F' b - ∑ a, M a b • frame F a)) :
    IsAdmissible Λ g F F' := by
  classical
  have key : ∀ a b, ∃ ξ c : 𝓞 E, M a b - (ξ : E) = (g : E) * (c : E) * M a b :=
    fun a b => exists_int_sub_eq_mul_of_integral_over g hg (M a b) (fun P hP => hint P hP a b)
  let ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E) := fun a b =>
    if b < a then 0 else if a = b then 1 else (key a b).choose
  have hξ : ∀ a b, ∃ c : 𝓞 E, M a b - ((ξ a b : 𝓞 E) : E) = (g : E) * (c : E) * M a b := by
    intro a b
    by_cases h1 : b < a
    · exact ⟨0, by simp [ξ, h1, hlow a b h1]⟩
    · by_cases h2 : a = b
      · subst h2; exact ⟨0, by simp [ξ, hdiag]⟩
      · obtain ⟨c, hc⟩ := (key a b).choose_spec
        exact ⟨c, by simpa [ξ, h1, h2] using hc⟩
  refine ⟨ξ, fun a b hab => by simp [ξ, hab], fun a => by simp [ξ], ?_⟩
  intro b P hP
  haveI := P.isPrime
  have hsplit : frame F' b - frameAct (frame F) ξ b =
      (frame F' b - ∑ a, M a b • frame F a) + ∑ a, (M a b - (ξ a b : E)) • frame F a := by
    simp only [frameAct, sub_smul, Finset.sum_sub_distrib]; abel
  rw [hsplit]
  refine Submodule.add_mem _ (hmod b P hP) (Submodule.sum_mem _ fun a _ => ?_)
  obtain ⟨c, hc⟩ := hξ a b
  obtain ⟨t, ht, htf⟩ := hloc P hP a
  obtain ⟨s, hs, o, ho⟩ := hint P hP a b
  refine ⟨s * t, P.asIdeal.primeCompl.mul_mem hs ht, ?_⟩
  rw [hc]
  have e : (s * t) • (((g : E) * (c : E) * M a b) • frame F a) =
      ((g : 𝓞 E) * (c * o)) • (t • frame F a) := by
    rw [← algebraMap_smul E (s * t), ← algebraMap_smul E ((g : 𝓞 E) * (c * o)),
      ← algebraMap_smul E t, smul_smul, smul_smul]
    congr 1
    simp only [map_mul, map_natCast]
    change (s : E) * (t : E) * ((g : E) * (c : E) * M a b) = (g : E) * ((c : E) * (o : E)) * (t : E)
    rw [← ho]; ring
  rw [e]
  exact Submodule.smul_mem_smul (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)) htf

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameAdmissibleOfCongrUnitriangularStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_admissible_of_congr_unitriangular : ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : StarRing E] {S : HSpace E} {r : ℕ} (Λ : Submodule (𝓞 E) S.V) (g : ℕ), g ≠ 0 → ∀ {T T' : E} (F : LFlag S r T) (F' : LFlag S r T') (M : Matrix (Fin (r + 1)) (Fin (r + 1)) E), (∀ a b, b < a → M a b = 0) → (∀ a, M a a = 1) → (∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∀ a b, ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∃ o : 𝓞 E, (s : E) * M a b = o) → (∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∀ a, frame F a ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ)) → (∀ b, ModG S Λ g (frame F' b - ∑ a, M a b • frame F a)) → IsAdmissible Λ g F F' := by
  first | exact @GlobalTheory.admissible_of_congr_unitriangular | exact GlobalTheory.admissible_of_congr_unitriangular | (intros; apply GlobalTheory.admissible_of_congr_unitriangular <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsTermTranslateByAdaptedLatticeAutomorphisms
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TransT

open IsDedekindDomain

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

def IA (P : HeightOneSpectrum (𝓞 E)) (x : E) : Prop :=
  ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∃ o : 𝓞 E, (s : E) * x = o

theorem one_nmem (P : HeightOneSpectrum (𝓞 E)) : (1 : 𝓞 E) ∉ P.asIdeal :=
  fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)

theorem mul_nmem (P : HeightOneSpectrum (𝓞 E)) {s t : 𝓞 E} (hs : s ∉ P.asIdeal) (ht : t ∉ P.asIdeal) :
    s * t ∉ P.asIdeal := fun h => (P.isPrime.mem_or_mem h).elim hs ht

theorem IA_coe (P : HeightOneSpectrum (𝓞 E)) (o : 𝓞 E) : IA P (o : E) := ⟨1, one_nmem P, o, by simp⟩

theorem IA_zero (P : HeightOneSpectrum (𝓞 E)) : IA P (0 : E) := by simpa using IA_coe P 0

theorem IA_one (P : HeightOneSpectrum (𝓞 E)) : IA P (1 : E) := by simpa using IA_coe P 1

theorem IA_add {P : HeightOneSpectrum (𝓞 E)} {x y : E} (hx : IA P x) (hy : IA P y) : IA P (x + y) := by
  obtain ⟨s, hs, o, e1⟩ := hx
  obtain ⟨t, ht, p, e2⟩ := hy
  refine ⟨s * t, mul_nmem P hs ht, t * o + s * p, ?_⟩
  push_cast
  linear_combination (t : E) * e1 + (s : E) * e2

theorem IA_mul {P : HeightOneSpectrum (𝓞 E)} {x y : E} (hx : IA P x) (hy : IA P y) : IA P (x * y) := by
  obtain ⟨s, hs, o, e1⟩ := hx
  obtain ⟨t, ht, p, e2⟩ := hy
  refine ⟨s * t, mul_nmem P hs ht, o * p, ?_⟩
  push_cast
  linear_combination ((t : E) * y) * e1 + (o : E) * e2

theorem IA_sum {P : HeightOneSpectrum (𝓞 E)} {ι : Type*} (s : Finset ι) (f : ι → E) (h : ∀ i, IA P (f i)) :
    IA P (∑ i ∈ s, f i) :=
  Finset.sum_induction f (IA P) (fun _ _ => IA_add) (IA_zero P) (fun i _ => h i)

theorem locP_smul (P : HeightOneSpectrum (𝓞 E)) (M : Submodule (𝓞 E) S.V) {k : E} (hk : IA P k) {x : S.V}
    (hx : x ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M)) :
    k • x ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M) := by
  obtain ⟨s, hs, o, ho⟩ := hk
  obtain ⟨t, ht, htx⟩ := hx
  refine ⟨s * t, P.asIdeal.primeCompl.mul_mem hs ht, ?_⟩
  have e : (s * t) • (k • x) = o • (t • x) := by
    rw [Formalism.L2.SG.Pf.smul_O, Formalism.L2.SG.Pf.smul_O o, Formalism.L2.SG.Pf.smul_O t, smul_smul, smul_smul]
    congr 1
    push_cast
    rw [← ho]; ring
  rw [e]
  exact M.smul_mem o htx

theorem modG_smul {Λ : Submodule (𝓞 E) S.V} {g : ℕ} {k : E}
    (hk : ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → IA P k) {x : S.V} (hx : ModG S Λ g x) :
    ModG S Λ g (k • x) := fun P hP => locP_smul P _ (hk P hP) (hx P hP)

theorem modG_sum {Λ : Submodule (𝓞 E) S.V} {g : ℕ} {ι : Type*} (s : Finset ι) (f : ι → S.V)
    (h : ∀ i, ModG S Λ g (f i)) : ModG S Λ g (∑ i ∈ s, f i) := fun P hP =>
  Submodule.sum_mem _ fun i _ => h i P hP

theorem mem_localization_aut (P : HeightOneSpectrum (𝓞 E)) {Λ : Submodule (𝓞 E) S.V} {a : S.V ≃ₗ[E] S.V}
    (ha : Formalism.HermitianLatticesTheory.gmap a Λ = Λ) {x : S.V} (hx : x ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ)) :
    a x ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ) := by
  haveI := P.isPrime
  rw [← ha, Formalism.L2.SG.Pf.gmap_locP, Formalism.L2.SG.Pf.gmap_apply_mem]
  exact hx

theorem frame_locP (Λ : Submodule (𝓞 E) S.V) (g : ℕ) {T : E} (F : LFlag S r T) (hconv : IsFixedConv Λ g F)
    (hl : IsLift Λ F) : ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∀ b,
      frame F b ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ) := by
  intro P hP b
  haveI := P.isPrime
  have hsub : ∀ (M : Submodule (𝓞 E) S.V), ∀ y ∈ M, y ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M :=
    fun M y hy => ⟨1, P.asIdeal.primeCompl.one_mem, by simpa using hy⟩
  refine Fin.lastCases ?_ (fun i => ?_) b
  · have e : frame F (Fin.last r) = F.fl.z := by simp [frame, FlagG.fvec]
    rw [e]; exact hsub _ _ hl.1
  · have e : frame F i.castSucc = F.fl.e i := by simp [frame, FlagG.fvec]
    rw [e]
    obtain ⟨c, -, hc1, hloc⟩ := hconv.1 P
    have he : F.fl.e i ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal
        (Submodule.span (𝓞 E) (Set.range fun a => c a • F.fl.e a)) := by
      refine hsub _ _ (Submodule.subset_span ⟨i, ?_⟩)
      simp [hc1 hP i]
    rw [← hloc] at he
    obtain ⟨t, ht, hte⟩ := he
    exact ⟨t, ht, (Submodule.mem_inf.1 hte).1⟩

def triM (w : Fin (r + 1) → Fin r → E) : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  fun c b => (if c = b then 1 else 0) + (if h : c.val < r then w b ⟨c.val, h⟩ else 0)

theorem triM_lower (w : Fin (r + 1) → Fin r → E) (hw : ∀ b (c : Fin r), b.val ≤ c.val → w b c = 0) :
    ∀ c b, b < c → triM w c b = 0 := by
  intro c b hbc
  unfold triM
  rw [if_neg hbc.ne']
  split_ifs with h
  · rw [hw b _ (le_of_lt (Fin.lt_def.1 hbc))]; simp
  · simp

theorem triM_diag (w : Fin (r + 1) → Fin r → E) (hw : ∀ b (c : Fin r), b.val ≤ c.val → w b c = 0) :
    ∀ b, triM w b b = 1 := by
  intro b
  unfold triM
  rw [if_pos rfl]
  split_ifs with h
  · rw [hw b _ le_rfl]; simp
  · simp

theorem triM_IA (P : HeightOneSpectrum (𝓞 E)) (w : Fin (r + 1) → Fin r → E) (hw : ∀ b c, IA P (w b c)) :
    ∀ c b, IA P (triM w c b) := by
  intro c b
  unfold triM
  refine IA_add ?_ ?_
  · split_ifs
    · exact IA_one P
    · exact IA_zero P
  · split_ifs
    · exact hw _ _
    · exact IA_zero P

theorem triM_sum {T : E} (F : LFlag S r T) (w : Fin (r + 1) → Fin r → E) (b : Fin (r + 1)) :
    ∑ c, triM w c b • frame F c = frame F b + ∑ i, w b i • F.fl.e i := by
  simp only [triM, add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  congr 1
  rw [Fin.sum_univ_castSucc]
  simp [frame, FlagG.fvec]

theorem mul_lower {n : ℕ} (A B : Matrix (Fin n) (Fin n) E) (hA : ∀ a b, b < a → A a b = 0)
    (hB : ∀ a b, b < a → B a b = 0) : ∀ a b, b < a → (A * B) a b = 0 := by
  intro a b hba
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun d _ => ?_
  rcases lt_or_ge d a with h | h
  · rw [hA a d h, zero_mul]
  · rw [hB d b (lt_of_lt_of_le hba h), mul_zero]

theorem mul_diag {n : ℕ} (A B : Matrix (Fin n) (Fin n) E) (hA : ∀ a b, b < a → A a b = 0)
    (hB : ∀ a b, b < a → B a b = 0) (hA1 : ∀ a, A a a = 1) (hB1 : ∀ a, B a a = 1) : ∀ a, (A * B) a a = 1 := by
  intro a
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · rw [hA1, hB1, one_mul]
  · intro d _ hd
    rcases lt_or_gt_of_ne hd with h | h
    · rw [hA a d h, zero_mul]
    · rw [hB d a h, mul_zero]
  · intro h; exact absurd (Finset.mem_univ a) h

theorem mul_IA {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (A B : Matrix (Fin n) (Fin n) E) (hA : ∀ a b, IA P (A a b))
    (hB : ∀ a b, IA P (B a b)) : ∀ a b, IA P ((A * B) a b) := by
  intro a b
  rw [Matrix.mul_apply]
  exact IA_sum _ _ fun d => IA_mul (hA a d) (hB d b)

theorem adapt_mat (Λ : Submodule (𝓞 E) S.V) (g : ℕ) {T : E} (F : LFlag S r T) (hconv : IsFixedConv Λ g F)
    (hl : IsLift Λ F) (a : S.V ≃ₗ[E] S.V) (haΛ : Formalism.HermitianLatticesTheory.gmap a Λ = Λ)
    (haf : ∀ b : Fin (r + 1), a (frame F b) - frame F b ∈ Xflag F b.val) :
    ∃ W : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ c b, b < c → W c b = 0) ∧ (∀ b, W b b = 1) ∧
      (∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∀ c b, IA P (W c b)) ∧
      ∀ b, a (frame F b) = ∑ c, W c b • frame F c := by
  have hloc := frame_locP Λ g F hconv hl
  have h := fun b : Fin (r + 1) => GlobalTheory.T.flag_coef_integral_of_local_integral Λ g F hconv b.val (a (frame F b) - frame F b) (haf b)
    (fun P hP => sub_mem (mem_localization_aut P haΛ (hloc P hP b)) (hloc P hP b))
  choose w hw0 hw1 hw2 using h
  refine ⟨triM w, triM_lower w hw1, triM_diag w hw1, fun P hP => triM_IA P w (fun b c => hw2 b P hP c), fun b => ?_⟩
  rw [triM_sum, ← hw0 b]
  abel

theorem map_lower {n : ℕ} (ξ : Matrix (Fin n) (Fin n) (𝓞 E)) (h : ∀ a b, b < a → ξ a b = 0) :
    ∀ a b, b < a → (ξ.map (fun x : 𝓞 E => (x : E))) a b = 0 := by
  intro a b hba; simp [h a b hba]

theorem map_diag {n : ℕ} (ξ : Matrix (Fin n) (Fin n) (𝓞 E)) (h : ∀ a, ξ a a = 1) :
    ∀ a, (ξ.map (fun x : 𝓞 E => (x : E))) a a = 1 := by
  intro a; simp [h a]

theorem isAdmissible_flagPair_of_unitriangular_left_automorphism (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (hg : g ≠ 0) {T T' : E} (F : LFlag S r T) (G : LFlag S r T')
    (a : S.V ≃ₗ[E] S.V) (haI : a ∈ Formalism.HermitianLatticesTheory.isom S.hT) (haΛ : Formalism.HermitianLatticesTheory.gmap a Λ = Λ)
    (haf : ∀ b : Fin (r + 1), a (frame F b) - frame F b ∈ Xflag F b.val) (hconv : IsFixedConv Λ g F)
    (hl : IsLift Λ F) (hA : IsAdmissible Λ g F G) :
    IsAdmissible Λ g F (Formalism.L2.SG.Saturated.mapL a haI G) := by
  have hA2 := (Formalism.L2.SG.Pf.IsAdmissible_mapL a haI g Λ F G).2 hA
  rw [haΛ] at hA2
  obtain ⟨ξ, hξ0, hξ1, hξc⟩ := hA2
  obtain ⟨W, hW0, hW1, hWi, hWe⟩ := adapt_mat Λ g F hconv hl a haΛ haf
  refine GlobalTheory.T.frame_admissible_of_congr_unitriangular Λ g hg F _ (W * ξ.map (fun x : 𝓞 E => (x : E)))
    (mul_lower _ _ hW0 (map_lower ξ hξ0)) (mul_diag _ _ hW0 (map_lower ξ hξ0) hW1 (map_diag ξ hξ1))
    (fun P hP => mul_IA P _ _ (hWi P hP) (fun a b => by simpa using IA_coe P (ξ a b)))
    (frame_locP Λ g F hconv hl) (fun b => ?_)
  have key : ∑ c, (W * ξ.map (fun x : 𝓞 E => (x : E))) c b • frame F c =
      frameAct (frame (Formalism.L2.SG.Saturated.mapL a haI F)) ξ b := by
    simp only [frameAct, Formalism.L2.SG.Saturated.frame_mapL, hWe, Matrix.mul_apply, Matrix.map_apply,
      Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]
  rw [key]
  exact hξc b

theorem isAdmissible_flagPair_of_unitriangular_right_automorphism (Λ Λ' : Submodule (𝓞 E) S.V) (g : ℕ) (hg : g ≠ 0) {T T' : E} (F : LFlag S r T)
    (F' : LFlag S r T') (γ a' : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (ha'I : a' ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (ha'Λ : Formalism.HermitianLatticesTheory.gmap a' Λ' = Λ') (ha'f : ∀ b : Fin (r + 1), a' (frame F' b) - frame F' b ∈ Xflag F' b.val)
    (hconv' : IsFixedConv Λ' g F') (hl' : IsLift Λ' F')
    (hFf : ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∀ a,
      frame F a ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ))
    (hA : IsAdmissible Λ g F (Formalism.L2.SG.Saturated.mapL γ hγ F')) :
    IsAdmissible Λ g F (Formalism.L2.SG.Saturated.mapL (γ * a'⁻¹) (Subgroup.mul_mem _ hγ (Subgroup.inv_mem _ ha'I)) F') := by
  obtain ⟨ξ, hξ0, hξ1, hξc⟩ := hA
  obtain ⟨K, hK0, hK1, hKi, hKe⟩ := adapt_mat Λ' g F' hconv' hl' a'⁻¹ (Formalism.L2.SG.Pf.gmap_inv ha'Λ)
    (GlobalTheory.T.inv_unitriangular_move_frame_mem_flagSubspace F' a' ha'f)
  refine GlobalTheory.T.frame_admissible_of_congr_unitriangular Λ g hg F _ (ξ.map (fun x : 𝓞 E => (x : E)) * K)
    (mul_lower _ _ (map_lower ξ hξ0) hK0) (mul_diag _ _ (map_lower ξ hξ0) hK0 (map_diag ξ hξ1) hK1)
    (fun P hP => mul_IA P _ _ (fun a b => by simpa using IA_coe P (ξ a b)) (hKi P hP))
    hFf (fun b => ?_)
  have key : frame (Formalism.L2.SG.Saturated.mapL (γ * a'⁻¹) (Subgroup.mul_mem _ hγ (Subgroup.inv_mem _ ha'I)) F') b -
      ∑ c, (ξ.map (fun x : 𝓞 E => (x : E)) * K) c b • frame F c =
      ∑ d, K d b • (frame (Formalism.L2.SG.Saturated.mapL γ hγ F') d - frameAct (frame F) ξ d) := by
    rw [Formalism.L2.SG.Saturated.frame_mapL, LinearEquiv.mul_apply, hKe b]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Formalism.L2.SG.Saturated.frame_mapL, map_sum, map_smul, frameAct, smul_sub, Finset.sum_sub_distrib,
      Matrix.mul_apply, Matrix.map_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]
  rw [key]
  exact modG_sum _ _ fun d => modG_smul (fun P hP => hKi P hP d b) (hξc d)

end Gen

theorem trans_main : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (t : TauC Y u u'), ∀ a ∈ Aut0 (lf D (X.Fu u)) t.lam, ∀ a' ∈ Aut0 (lf D (X.Fu u')) t.lam', ∃ s : TauC Y u u', s.lam = t.lam ∧ s.lam' = t.lam' ∧ ∃ n ∈ NLam t.lam (lf D (X.Fu u)), ∃ n' ∈ NLam t.lam' (lf D (X.Fu u')), s.lin = n * (a * t.lin * a'⁻¹) * n' := by
  intro D X Y u u' t a ha a' ha'
  have hγ : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have hγΛ : Formalism.HermitianLatticesTheory.gmap t.lin t.lam' = t.lam := t.rep.2.2.2.1
  have hPD := t.rep.2.2.2.2
  have haI : a ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := ha.1.1
  have ha'I : a' ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := ha'.1.1
  have hβ : a * t.lin * a'⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ haI hγ) (Subgroup.inv_mem _ ha'I)
  have hβΛ : Formalism.HermitianLatticesTheory.gmap (a * t.lin * a'⁻¹) t.lam' = t.lam := by
    rw [Formalism.L2.SG.Pf.gmap_mul, Formalism.L2.SG.Pf.gmap_inv ha'.2, Formalism.L2.SG.Pf.gmap_mul, hγΛ, ha.2]
  obtain ⟨x, hx⟩ := Formalism.L2.SG.Pf.ratPt_holds D X _ hβ
  have hPDβ : Formalism.L2.SG.TermDef.PD D t.lam (lf D (X.Fu u)) u' (mapLF (a * t.lin * a'⁻¹) (lf D (X.Fu u'))) := by
    have hRow := (Y.rowsOK u).1 _ t.mem
    have hRow' := (Y.rowsOK u').1 _ t.mem'
    have hFO' : FrameOK D t.lam' (lf D (X.Fu u')) := ⟨hRow'.2.1.2.2.2, hRow'.2.2⟩
    have hg : Formalism.MainNotions.S.Lat.gS D ≠ 0 := by
      unfold Formalism.MainNotions.S.Lat.gS; exact Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
    have emap : ∀ (β : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hβ : β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) {T : D.host.E}
        (F : LFlag (D.sp.Y 0) D.R.rS T), mapLF β F = Formalism.L2.SG.Saturated.mapL β hβ F := by
      intro β hβ T F; unfold mapLF; rw [dite_eq_left hβ]; rfl
    refine ⟨?_, ?_, GlobalTheory.FrameIsom.frameOK_mapLF D _ hβ t.lam' t.lam hβΛ _ _ hFO'⟩
    · rw [emap _ hβ, ← hβΛ]; exact (Formalism.L2.SG.Pf.IsLift_mapL _ hβ _ _).2 hRow'.2.1.2.2.1
    · have hA : IsAdmissible t.lam (Formalism.MainNotions.S.Lat.gS D) (lf D (X.Fu u)) (Formalism.L2.SG.Saturated.mapL t.lin hγ (lf D (X.Fu u'))) := by
        rw [← emap]; exact hPD.2.1
      have hβ2 : t.lin * a'⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := Subgroup.mul_mem _ hγ (Subgroup.inv_mem _ ha'I)
      have e : Formalism.L2.SG.Saturated.mapL (a * t.lin * a'⁻¹) hβ (lf D (X.Fu u')) =
          Formalism.L2.SG.Saturated.mapL a haI (Formalism.L2.SG.Saturated.mapL (t.lin * a'⁻¹) hβ2 (lf D (X.Fu u'))) := by
        rw [← Formalism.L2.SG.Saturated.mapL_mul]
        congr 1
      rw [emap _ hβ]
      refine (congrArg (fun G => IsAdmissible t.lam (Formalism.MainNotions.S.Lat.gS D) (lf D (X.Fu u)) G) e).mpr ?_
      exact isAdmissible_flagPair_of_unitriangular_left_automorphism t.lam (Formalism.MainNotions.S.Lat.gS D) hg (lf D (X.Fu u))
        (Formalism.L2.SG.Saturated.mapL (t.lin * a'⁻¹) hβ2 (lf D (X.Fu u'))) a haI ha.2 ha.1.2 hRow.2.1.2.2.2 hRow.2.1.2.2.1
        (isAdmissible_flagPair_of_unitriangular_right_automorphism t.lam t.lam' (Formalism.MainNotions.S.Lat.gS D) hg (lf D (X.Fu u)) (lf D (X.Fu u')) t.lin a' hγ ha'I ha'.2 ha'.1.2
          hRow'.2.1.2.2.2 hRow'.2.1.2.2.1 (frame_locP t.lam (Formalism.MainNotions.S.Lat.gS D) _ hRow.2.1.2.2.2 hRow.2.1.2.2.1) hA)
  let p : GCar X u u' (X.Fu u) (X.Fu u') t.lam t.lam' := ⟨(x, a * t.lin * a'⁻¹), hx, hβ, hβΛ, hPDβ⟩
  let s : TauC Y u u' := ⟨t.lam, t.mem, t.lam', t.mem', Quot.mk _ p⟩
  refine ⟨s, rfl, rfl, ?_⟩
  have heq : Equivalence (GRel X u u' (X.Fu u) (X.Fu u') t.lam t.lam') := by
    refine ⟨fun p => ⟨1, (Formalism.L2.SG.Pf.NLamSub _ _).one_mem, 1, (Formalism.L2.SG.Pf.NLamSub _ _).one_mem, by simp⟩, ?_, ?_⟩
    · rintro p q ⟨n, hn, n', hn', e⟩
      refine ⟨n⁻¹, (Formalism.L2.SG.Pf.NLamSub t.lam _).inv_mem hn, n'⁻¹, (Formalism.L2.SG.Pf.NLamSub t.lam' _).inv_mem hn', ?_⟩
      rw [e]; group
    · rintro p q w ⟨n, hn, n', hn', e⟩ ⟨m, hm, m', hm', e'⟩
      refine ⟨m * n, (Formalism.L2.SG.Pf.NLamSub t.lam _).mul_mem hm hn, n' * m', (Formalism.L2.SG.Pf.NLamSub t.lam' _).mul_mem hn' hm', ?_⟩
      rw [e', e]; group
  have hq : GRel X u u' (X.Fu u) (X.Fu u') t.lam t.lam' p s.rep := by
    have h1 : Quot.mk (GRel X u u' (X.Fu u) (X.Fu u') t.lam t.lam') s.rep = Quot.mk _ p := Quot.out_eq _
    exact heq.symm ((heq.eqvGen_iff).1 (Quot.eqvGen_exact h1))
  obtain ⟨n, hn, n', hn', e⟩ := hq
  exact ⟨n, hn, n', hn', e⟩

end GlobalTheory.TransT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsTermTranslateByAdaptedLatticeAutomorphismsStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_term_translate_by_adapted_lattice_automorphisms : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (t : TauC Y u u'), ∀ a ∈ Aut0 (lf D (X.Fu u)) t.lam, ∀ a' ∈ Aut0 (lf D (X.Fu u')) t.lam', ∃ s : TauC Y u u', s.lam = t.lam ∧ s.lam' = t.lam' ∧ ∃ n ∈ NLam t.lam (lf D (X.Fu u)), ∃ n' ∈ NLam t.lam' (lf D (X.Fu u')), s.lin = n * (a * t.lin * a'⁻¹) * n' := by
  first | exact @GlobalTheory.TransT.trans_main | exact GlobalTheory.TransT.trans_main | (intros; apply GlobalTheory.TransT.trans_main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BaseFrameLatticeInvariantUnderAdaptedTranslate
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BaseFrameLatticeInvariantUnderAdaptedTranslate
noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.TgTr

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

def Hom {T T' : E} (φ : S.V ≃ₗ[E] S.V) (A : LFlag S r T) (B : LFlag S r T') : Prop :=
  ∀ a : Fin (r + 1), φ (frame A a) - frame B a ∈ Xflag B a.val

theorem frame_castSucc {T : E} (A : LFlag S r T) (i : Fin r) : frame A i.castSucc = A.fl.e i := by
  simp [frame, FlagG.fvec, Fin.snoc_castSucc]

theorem frame_last {T : E} (A : LFlag S r T) : frame A (Fin.last r) = A.fl.z := by
  simp [frame, FlagG.fvec, Fin.snoc_last]

theorem xflag_mono {T : E} (A : LFlag S r T) {i j : ℕ} (h : i ≤ j) : Xflag A i ≤ Xflag A j := by
  exact Submodule.span_mono (Set.image_mono (fun k hk => lt_of_lt_of_le hk h))

theorem e_mem_xflag {T : E} (A : LFlag S r T) (i : Fin r) {j : ℕ} (h : i.1 < j) : A.fl.e i ∈ Xflag A j :=
  Submodule.subset_span ⟨i, h, rfl⟩

theorem Hom.map_mem {T T' : E} {φ : S.V ≃ₗ[E] S.V} {A : LFlag S r T} {B : LFlag S r T'} (h : Hom φ A B)
    (j : ℕ) {x : S.V} (hx : x ∈ Xflag A j) : φ x ∈ Xflag B j := by
  have hle : Xflag A j ≤ (Xflag B j).comap (φ : S.V →ₗ[E] S.V) := by
    apply Submodule.span_le.mpr
    rintro y ⟨i, hi, rfl⟩
    have h1 := h i.castSucc
    rw [frame_castSucc, frame_castSucc] at h1
    have h2 : φ (A.fl.e i) = (φ (A.fl.e i) - B.fl.e i) + B.fl.e i := by abel
    show φ (A.fl.e i) ∈ Xflag B j
    rw [h2]
    refine Submodule.add_mem _ ?_ (e_mem_xflag B i hi)
    exact xflag_mono B (le_of_lt hi) h1
  exact hle hx

theorem Hom.comp {T T' T'' : E} {φ ψ : S.V ≃ₗ[E] S.V} {A : LFlag S r T} {B : LFlag S r T'} {C : LFlag S r T''}
    (hφ : Hom φ B C) (hψ : Hom ψ A B) : Hom (φ * ψ) A C := by
  intro a
  have e1 : (φ * ψ) (frame A a) - frame C a = φ (ψ (frame A a) - frame B a) + (φ (frame B a) - frame C a) := by
    rw [LinearEquiv.mul_apply, map_sub]; abel
  rw [e1]
  exact Submodule.add_mem _ (hφ.map_mem _ (hψ a)) (hφ a)

theorem Hom.inv {T : E} {φ : S.V ≃ₗ[E] S.V} {A : LFlag S r T} (h : Hom φ A A) : Hom φ⁻¹ A A := by
  have hW : ∀ j : ℕ, ∀ x ∈ Xflag A j, φ⁻¹ x ∈ Xflag A j := by
    intro j x hx
    set W := Xflag A j
    have : FiniteDimensional E W := FiniteDimensional.span_of_finite E ((Set.toFinite _).image _)
    have hle : W.map (φ : S.V →ₗ[E] S.V) ≤ W := by
      rintro y ⟨w, hw, rfl⟩
      exact h.map_mem j hw
    have heq : W.map (φ : S.V →ₗ[E] S.V) = W :=
      Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq φ W)
    rw [← heq] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    have : φ⁻¹ (φ w) = w := by
      rw [← LinearEquiv.mul_apply, inv_mul_cancel]; rfl
    simpa [this] using hw
  intro a
  have e1 : φ⁻¹ (frame A a) - frame A a = -(φ⁻¹ (φ (frame A a) - frame A a)) := by
    have : φ⁻¹ (φ (frame A a)) = frame A a := by
      rw [← LinearEquiv.mul_apply, inv_mul_cancel]; rfl
    rw [map_sub, this]; abel
  rw [e1]
  exact Submodule.neg_mem _ (hW _ _ (h a))

theorem xflag_r {T : E} (A : LFlag S r T) : Xflag A r = Xsp A := by
  show Submodule.span E (A.fl.e '' {i | i.1 < r}) = Submodule.span E (Set.range A.fl.e)
  congr 1
  rw [← Set.image_univ]
  congr 1
  ext i; simp

theorem z_mem_orth {T : E} (A : LFlag S r T) : A.fl.z ∈ orth S (Xsp A) := by
  have hle : Xsp A ≤ LinearMap.ker (S.hT.flip A.fl.z) := by
    apply Submodule.span_le.mpr
    rintro y ⟨i, rfl⟩
    show S.hT.flip A.fl.z (A.fl.e i) = 0
    rw [LinearMap.flip_apply]; exact A.fl.z_orth i
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  intro x hx
  have := hle hx
  rw [LinearMap.mem_ker, LinearMap.flip_apply] at this
  exact this

theorem Hom.of_nlam {T : E} {Λ : Submodule (𝓞 E) S.V} {n : S.V ≃ₗ[E] S.V} {A : LFlag S r T}
    (h : n ∈ NLam Λ A) : Hom n A A := by
  obtain ⟨-, h2, h3⟩ := h
  intro a
  induction a using Fin.lastCases with
  | last =>
    rw [frame_last, Fin.val_last, xflag_r]
    exact h3 _ (z_mem_orth A)
  | cast i =>
    rw [frame_castSucc, Fin.val_castSucc]
    exact h2 i.1 _ (e_mem_xflag A i (Nat.lt_succ_self _))

theorem frame_mapLF {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (A : LFlag S r T) (a : Fin (r + 1)) :
    frame (mapLF γ A) a = γ (frame A a) := by
  induction a using Fin.lastCases with
  | last => simp [mapLF, hγ, frame_last, mapFlag]
  | cast i => simp [mapLF, hγ, frame_castSucc, mapFlag]

theorem Hom.of_mapLF {T : E} {γ : S.V ≃ₗ[E] S.V} (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (A : LFlag S r T) :
    Hom γ A (mapLF γ A) := by
  intro a
  rw [frame_mapLF hγ, sub_self]
  exact Submodule.zero_mem _

theorem gmap_mul (φ ψ : S.V ≃ₗ[E] S.V) (Λ : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.gmap (φ * ψ) Λ = Formalism.HermitianLatticesTheory.gmap φ (Formalism.HermitianLatticesTheory.gmap ψ Λ) := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨ψ y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem gmap_inv {φ : S.V ≃ₗ[E] S.V} {Λ : Submodule (𝓞 E) S.V} (h : Formalism.HermitianLatticesTheory.gmap φ Λ = Λ) :
    Formalism.HermitianLatticesTheory.gmap φ⁻¹ Λ = Λ := by
  conv_lhs => rw [← h]
  rw [← gmap_mul, inv_mul_cancel]
  ext x
  simp [Formalism.HermitianLatticesTheory.gmap]

end GlobalTheory.Unfold.TgTr

namespace GlobalTheory.Unfold


open GlobalTheory.Unfold.TgTr in
theorem tg_translate : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (t₀ s : TauC Y u u') (Λ₀ : LV D) (a a' n n' : GV D), TG F F' t₀ Λ₀ → a ∈ Aut0 (lf D (X.Fu u)) t₀.lam → a' ∈ Aut0 (lf D (X.Fu u')) t₀.lam' → n ∈ NLam t₀.lam (lf D (X.Fu u)) → n' ∈ NLam t₀.lam' (lf D (X.Fu u')) → s.lam = t₀.lam → s.lin = n * (a * t₀.lin * a'⁻¹) * n' → TG F F' s Λ₀ := by
  intro D X Y u u' F F' t₀ s Λ₀ a a' n n' hTG ha ha' hn hn' hsl hsg
  obtain ⟨g, hgL, hgt, hΛ⟩ := hTG
  obtain ⟨⟨haI, haH⟩, haΛ⟩ := ha
  obtain ⟨⟨ha'I, ha'H⟩, -⟩ := ha'
  have hnH : Hom n _ _ := Hom.of_nlam hn
  have hn'H : Hom n' _ _ := Hom.of_nlam hn'
  have hnI : n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hn.1.1
  have hnΛ : Formalism.HermitianLatticesTheory.gmap n t₀.lam = t₀.lam := hn.1.2
  have ht₀I : t₀.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t₀.rep.2.2.1
  have hsI : s.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := s.rep.2.2.1
  refine ⟨g * a⁻¹ * n⁻¹, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgL.1 (Subgroup.inv_mem _ haI)) (Subgroup.inv_mem _ hnI)
  · exact Hom.comp (Hom.comp (φ := g) hgL.2 (Hom.inv haH)) (Hom.inv hnH)
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgL.1 (Subgroup.inv_mem _ haI)) (Subgroup.inv_mem _ hnI)
  · have hK : Hom (g * t₀.lin * a'⁻¹ * n') (lf D (X.Fu u')) F' :=
      Hom.comp (Hom.comp (Hom.comp (φ := g) hgt.2 (Hom.of_mapLF ht₀I _)) (Hom.inv ha'H)) hn'H
    have heq : g * a⁻¹ * n⁻¹ * s.lin = g * t₀.lin * a'⁻¹ * n' := by
      rw [hsg]; group
    intro c
    have hf : frame s.frame c = s.lin (frame (lf D (X.Fu u')) c) := frame_mapLF hsI _ c
    rw [hf, ← LinearEquiv.mul_apply, heq]
    exact hK c
  · rw [hsl, gmap_mul, gmap_mul, gmap_inv hnΛ, gmap_inv haΛ, hΛ]

end GlobalTheory.Unfold
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BaseFrameLatticeInvariantUnderAdaptedTranslateStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseFrameLattice_invariant_under_adapted_translate : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (t₀ s : TauC Y u u') (Λ₀ : LV D) (a a' n n' : GV D), TG F F' t₀ Λ₀ → a ∈ Aut0 (lf D (X.Fu u)) t₀.lam → a' ∈ Aut0 (lf D (X.Fu u')) t₀.lam' → n ∈ NLam t₀.lam (lf D (X.Fu u)) → n' ∈ NLam t₀.lam' (lf D (X.Fu u')) → s.lam = t₀.lam → s.lin = n * (a * t₀.lin * a'⁻¹) * n' → TG F F' s Λ₀ := by
  first | exact @GlobalTheory.Unfold.tg_translate | exact GlobalTheory.Unfold.tg_translate | (intros; apply GlobalTheory.Unfold.tg_translate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitCountRowsDoubleCosetsInnerDatumClass
noncomputable section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OrbitCount

theorem relIndex_prod_prod {G G' : Type} [Group G] [Group G'] (H K : Subgroup G) (H' K' : Subgroup G') :
    (H.prod H').relIndex (K.prod K') = H.relIndex K * H'.relIndex K' := by
  unfold Subgroup.relIndex
  rw [← Subgroup.index_prod,
    ← Subgroup.index_comap_of_surjective ((H.subgroupOf K).prod (H'.subgroupOf K'))
      (f := (Subgroup.prodEquiv K K').toMonoidHom) (Subgroup.prodEquiv K K').surjective]
  congr 1

theorem card_image_eq_relIndex {Γ α : Type} [Group Γ] (P B : Subgroup Γ) (f : Γ → α)
    (hf : ∀ p ∈ P, ∀ q ∈ P, f p = f q ↔ p⁻¹ * q ∈ B) :
    Nat.card (f '' (P : Set Γ)) = B.relIndex P := by
  unfold Subgroup.relIndex Subgroup.index
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (Quotient.lift (s := QuotientGroup.leftRel (B.subgroupOf P))
      (fun p : P => (⟨f p, p, p.2, rfl⟩ : f '' (P : Set Γ))) ?_) ⟨?_, ?_⟩)
  · intro a b h
    have h' := QuotientGroup.leftRel_apply.mp h
    apply Subtype.ext
    exact (hf a a.2 b b.2).2 (by simpa [Subgroup.mem_subgroupOf] using h')
  · intro x y hxy
    induction x using Quotient.inductionOn with | h a => ?_
    induction y using Quotient.inductionOn with | h b => ?_
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.mpr
    have := congrArg Subtype.val hxy
    simp only [Quotient.lift_mk] at this
    simpa [Subgroup.mem_subgroupOf] using (hf a a.2 b b.2).1 this
  · rintro ⟨_, p, hp, rfl⟩
    exact ⟨Quotient.mk _ ⟨p, hp⟩, rfl⟩

theorem lrel_refl {D : D7} {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') (Λ : LV D) :
    LRel F F' Λ Λ := by
  refine ⟨1, ⟨(Formalism.HermitianLatticesTheory.isom (VS D).hT).one_mem, fun a => rfl, fun a => rfl⟩, ?_⟩
  congr 1
  simp [Formalism.HermitianLatticesTheory.gmap]

end GlobalTheory.OrbitCount

namespace GlobalTheory.OrbitCount

theorem orbit_count : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (t₀ : TauC Y u u') (Λ₀ : LV D), TG F F' t₀ Λ₀ → ∀ K, K = {κ | ∃ (t : TauC Y u u') (Λ₁ : LV D), TG F F' t Λ₁ ∧ LRel F F' Λ₀ Λ₁ ∧ key t = κ} → K.Finite ∧ (∀ κ ∈ K, ∃ t : TauC Y u u', TG F F' t Λ₀ ∧ key t = κ) ∧ (∀ (t : TauC Y u u') (Λ₁ : LV D), TG F F' t Λ₁ → LRel F F' Λ₀ Λ₁ → wt t = wt t₀) ∧ (K.encard : ℝ≥0∞) * ENNReal.ofReal (wt t₀ ^ 2) = (((stabL F F' Λ₀).encard : ℝ≥0∞))⁻¹ := by
  intro D X Y u u' F F' w hw hG t₀ Λ₀ h₀ K hK
  obtain ⟨A, N, hA, hN, hNA, hNn, hiA, hcA⟩ := GlobalTheory.T.rowLattice_automorphisms_eq_adapted_mod_unipotent D X Y u u' t₀.lam t₀.mem
  obtain ⟨A', N', hA', hN', hNA', hNn', hiA', hcA'⟩ := GlobalTheory.T.rowLattice_automorphisms_eq_adapted_mod_unipotent D X Y u' u t₀.lam' t₀.mem'
  obtain ⟨B, hB, hNB, hBiff⟩ := GlobalTheory.T.exists_subgroup_unitriangular_pairs_keeping_doubleCoset D X Y u u' t₀
  have hS := GlobalTheory.T.card_stabilizer_innerDatum_rowDoubleCoset D X Y u u' F F' w hw hG t₀ Λ₀ h₀ B N N' hB hN hN'
  have mA : ∀ a, a ∈ A ↔ a ∈ Aut0 (lf D (X.Fu u)) t₀.lam := fun a => SetLike.mem_coe.symm.trans (Set.ext_iff.mp hA a)
  have mA' : ∀ a, a ∈ A' ↔ a ∈ Aut0 (lf D (X.Fu u')) t₀.lam' := fun a => SetLike.mem_coe.symm.trans (Set.ext_iff.mp hA' a)
  have mN : ∀ a, a ∈ N ↔ a ∈ NLam t₀.lam (lf D (X.Fu u)) := fun a => SetLike.mem_coe.symm.trans (Set.ext_iff.mp hN a)
  have mN' : ∀ a, a ∈ N' ↔ a ∈ NLam t₀.lam' (lf D (X.Fu u')) := fun a => SetLike.mem_coe.symm.trans (Set.ext_iff.mp hN' a)
  set P : Subgroup (GV D × GV D) := A.prod A' with hP
  have htr : ∀ p : GV D × GV D, ∃ s : TauC Y u u', p ∈ P → (s.lam = t₀.lam ∧ s.lam' = t₀.lam' ∧
      ∃ n ∈ NLam t₀.lam (lf D (X.Fu u)), ∃ n' ∈ NLam t₀.lam' (lf D (X.Fu u')), s.lin = n * (p.1 * t₀.lin * p.2⁻¹) * n') := by
    intro p
    by_cases hp : p ∈ P
    · obtain ⟨s, h1, h2, n, hn, n', hn', h3⟩ := GlobalTheory.T.exists_term_translate_by_adapted_lattice_automorphisms D X Y u u' t₀ p.1 ((mA _).1 hp.1) p.2 ((mA' _).1 hp.2)
      exact ⟨s, fun _ => ⟨h1, h2, n, hn, n', hn', h3⟩⟩
    · exact ⟨t₀, fun h => absurd h hp⟩
  choose s hs using htr
  have hTG : ∀ p ∈ P, TG F F' (s p) Λ₀ := by
    intro p hp
    obtain ⟨h1, -, n, hn, n', hn', h3⟩ := hs p hp
    exact GlobalTheory.T.baseFrameLattice_invariant_under_adapted_translate D X Y u u' F F' t₀ (s p) Λ₀ p.1 p.2 n n' h₀ ((mA _).1 hp.1) ((mA' _).1 hp.2) hn hn' h1 h3

  have hfib : ∀ p ∈ P, ∀ q ∈ P, key (s p) = key (s q) ↔ p⁻¹ * q ∈ B := by
    intro p hp q hq
    obtain ⟨hp1, hp2, n, hn, n', hn', hpl⟩ := hs p hp
    obtain ⟨hq1, hq2, m, hm, m', hm', hql⟩ := hs q hq
    rw [GlobalTheory.T.term_row_double_coset_eq_iff_isometries D X Y u u' (s p) (s q), hp1, hq1, hp2, hq2]
    simp only [true_and]
    have ep : (s p).lin = (n * p.1) * t₀.lin * (n'⁻¹ * p.2)⁻¹ := by rw [hpl]; group
    have eq : (s q).lin = (m * q.1) * t₀.lin * (m'⁻¹ * q.2)⁻¹ := by rw [hql]; group
    have hnA : n ∈ A := hNA ((mN n).2 hn)
    have hmA : m ∈ A := hNA ((mN m).2 hm)
    have hnA' : n'⁻¹ ∈ A' := A'.inv_mem (hNA' ((mN' n').2 hn'))
    have hmA' : m'⁻¹ ∈ A' := A'.inv_mem (hNA' ((mN' m').2 hm'))
    rw [ep, eq, hBiff (n * p.1) ((mA _).1 (A.mul_mem hnA hp.1)) (m * q.1) ((mA _).1 (A.mul_mem hmA hq.1))
      (n'⁻¹ * p.2) ((mA' _).1 (A'.mul_mem hnA' hp.2)) (m'⁻¹ * q.2) ((mA' _).1 (A'.mul_mem hmA' hq.2))]
    have hx : p.1⁻¹ * (n⁻¹ * m) * p.1⁻¹⁻¹ ∈ N :=
      hNn _ (A.inv_mem hp.1) _ (N.mul_mem (N.inv_mem ((mN n).2 hn)) ((mN m).2 hm))
    have hx' : p.2⁻¹ * (n' * m'⁻¹) * p.2⁻¹⁻¹ ∈ N' :=
      hNn' _ (A'.inv_mem hp.2) _ (N'.mul_mem ((mN' n').2 hn') (N'.inv_mem ((mN' m').2 hm')))
    have hmB : (p.1⁻¹ * (n⁻¹ * m) * p.1⁻¹⁻¹, p.2⁻¹ * (n' * m'⁻¹) * p.2⁻¹⁻¹) ∈ B :=
      hNB _ ((mN _).1 hx) _ ((mN' _).1 hx')
    have heq : ((n * p.1)⁻¹ * (m * q.1), (n'⁻¹ * p.2)⁻¹ * (m'⁻¹ * q.2)) =
        (p.1⁻¹ * (n⁻¹ * m) * p.1⁻¹⁻¹, p.2⁻¹ * (n' * m'⁻¹) * p.2⁻¹⁻¹) * (p⁻¹ * q) := by
      ext <;> simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv] <;> group
    rw [heq, B.mul_mem_cancel_left hmB]

  have hKim : K = (fun p => key (s p)) '' (P : Set (GV D × GV D)) := by
    rw [hK]
    ext κ
    constructor
    · rintro ⟨t, Λ₁, ht, hrel, rfl⟩
      obtain ⟨a, ha, a', ha', hkey⟩ := GlobalTheory.T.matching_translate_same_row_double_coset D X Y u u' F F' w hw hG t₀ t Λ₀ Λ₁ h₀ ht hrel
      have hp : (a, a') ∈ P := ⟨(mA a).2 ha, (mA' a').2 ha'⟩
      obtain ⟨h1, h2, n, hn, n', hn', h3⟩ := hs (a, a') hp
      exact ⟨(a, a'), hp, hkey (s (a, a')) h1 h2 ⟨n, hn, n', hn', h3⟩⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨s p, Λ₀, hTG p hp, lrel_refl F F' Λ₀, rfl⟩
  have hcardK : Nat.card K = B.relIndex P := by
    rw [hKim]; exact card_image_eq_relIndex P B _ hfib
  have hBP : B ≤ P := fun b hb => ⟨(mA _).2 ((hB b).1 hb).1, (mA' _).2 ((hB b).1 hb).2.1⟩
  have hNNB : N.prod N' ≤ B := fun b hb => by
    have := hNB b.1 ((mN _).1 hb.1) b.2 ((mN' _).1 hb.2)
    simpa using this
  have hprod : (N.prod N').relIndex B * B.relIndex P = Nat.card (autLz D (X.Fu u) t₀.lam) * Nat.card (autLz D (X.Fu u') t₀.lam') := by
    rw [Subgroup.relIndex_mul_relIndex _ _ _ hNNB hBP, hP, relIndex_prod_prod, hiA, hiA']
  set k := B.relIndex P with hk
  set m := (N.prod N').relIndex B with hm
  set c := Nat.card (autLz D (X.Fu u) t₀.lam) with hc
  set c' := Nat.card (autLz D (X.Fu u') t₀.lam') with hc'
  have hmk : 0 < m * k := by rw [hprod]; exact Nat.mul_pos hcA hcA'
  have hk0 : 0 < k := Nat.pos_of_mul_pos_left hmk
  have hm0 : 0 < m := Nat.pos_of_mul_pos_right hmk
  have hKfin : K.Finite := by
    have : 0 < Nat.card K := hcardK ▸ hk0
    exact Set.finite_coe_iff.mp (Nat.card_pos_iff.mp this).2
  have hSfin : (stabL F F' Λ₀).Finite := by
    have : 0 < Nat.card (stabL F F' Λ₀) := hS ▸ hm0
    exact Set.finite_coe_iff.mp (Nat.card_pos_iff.mp this).2
  have hKenc : K.encard = (k : ℕ∞) := by
    rw [← hKfin.cast_ncard_eq, ← Nat.card_coe_set_eq, hcardK]
  have hSenc : (stabL F F' Λ₀).encard = (m : ℕ∞) := by
    rw [← hSfin.cast_ncard_eq, ← Nat.card_coe_set_eq, hS]
  have hwt : ∀ (t : TauC Y u u'), t.lam = t₀.lam → t.lam' = t₀.lam' → wt t = wt t₀ := by
    intro t h1 h2
    simp only [wt, h1, h2]
  refine ⟨hKfin, ?_, ?_, ?_⟩
  · intro κ hκ
    rw [hKim] at hκ
    obtain ⟨p, hp, rfl⟩ := hκ
    exact ⟨s p, hTG p hp, rfl⟩
  · intro t Λ₁ ht hrel
    obtain ⟨h1, h2, -⟩ := GlobalTheory.T.terms_same_rational_inner_class_are_translates D X Y u u' F F' w hw hG t₀ t Λ₀ Λ₁ h₀ ht hrel
    exact hwt t h1 h2
  · have hw2 : wt t₀ ^ 2 = (c : ℝ)⁻¹ * (c' : ℝ)⁻¹ := by
      simp only [wt]
      rw [Real.sq_sqrt (by unfold wRow; positivity)]
      rfl
    rw [hKenc, hSenc, hw2, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_inv_of_pos (by exact_mod_cast hcA), ENNReal.ofReal_inv_of_pos (by exact_mod_cast hcA'),
      ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
    have hcc : ((c : ℝ≥0∞))⁻¹ * ((c' : ℝ≥0∞))⁻¹ = ((m : ℝ≥0∞))⁻¹ * ((k : ℝ≥0∞))⁻¹ := by
      rw [← ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _)),
        ← ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]
      congr 1
      exact_mod_cast hprod.symm
    simp only [ENat.toENNReal_coe]
    rw [hcc, mul_comm, mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast hk0.ne') (ENNReal.natCast_ne_top _), mul_one]

end GlobalTheory.OrbitCount
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitCountRowsDoubleCosetsInnerDatumClassStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbitCount_rows_doubleCosets_innerDatum_class : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (t₀ : TauC Y u u') (Λ₀ : LV D), TG F F' t₀ Λ₀ → ∀ K, K = {κ | ∃ (t : TauC Y u u') (Λ₁ : LV D), TG F F' t Λ₁ ∧ LRel F F' Λ₀ Λ₁ ∧ key t = κ} → K.Finite ∧ (∀ κ ∈ K, ∃ t : TauC Y u u', TG F F' t Λ₀ ∧ key t = κ) ∧ (∀ (t : TauC Y u u') (Λ₁ : LV D), TG F F' t Λ₁ → LRel F F' Λ₀ Λ₁ → wt t = wt t₀) ∧ (K.encard : ℝ≥0∞) * ENNReal.ofReal (wt t₀ ^ 2) = (((stabL F F' Λ₀).encard : ℝ≥0∞))⁻¹ := by
  first | exact @GlobalTheory.OrbitCount.orbit_count | exact GlobalTheory.OrbitCount.orbit_count | (intros; apply GlobalTheory.OrbitCount.orbit_count <;> assumption)
end
