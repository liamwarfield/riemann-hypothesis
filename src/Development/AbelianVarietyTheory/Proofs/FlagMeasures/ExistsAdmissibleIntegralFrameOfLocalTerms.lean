module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryPointsDiscreteFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnLevelStabTriv
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGlobalUnitriangularOfLocalCongruence

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovedReferenceFrameCongruentUnitriangular
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovesToGivesIntegralMatrices
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UpperUnitriangularMul
namespace GlobalTheory.UpperUnitriangularMul

open Matrix

theorem upperUnitriangular_mul {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}
    {U W : Matrix (Fin N) (Fin N) E}
    (hU : ∀ a b : Fin N, b < a → U a b = (0 : E)) (hU1 : ∀ a : Fin N, U a a = (1 : E))
    (hW : ∀ a b : Fin N, b < a → W a b = (0 : E)) (hW1 : ∀ a : Fin N, W a a = (1 : E)) :
    (∀ a b : Fin N, b < a → (U * W) a b = (0 : E)) ∧ ∀ a : Fin N, (U * W) a a = (1 : E) := by
  constructor
  · intro a b hba
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro c _
    rcases lt_or_ge c a with h | h
    · rw [hU a c h, zero_mul]
    · rw [hW c b (lt_of_lt_of_le hba h), mul_zero]
  · intro a
    rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hU1, hW1, one_mul]
    · intro c _ hca
      rcases lt_or_gt_of_ne hca with h | h
      · rw [hU a c h, zero_mul]
      · rw [hW c a h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ a) h

end GlobalTheory.UpperUnitriangularMul
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovesToGivesIntegralMatrices
noncomputable section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MovedFrames

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem exists_coef_of_mem_span_image {V : Type*} [AddCommGroup V] [Module E V] (e : Fin r → V)
    (s : Set (Fin r)) {x : V} (hx : x ∈ Submodule.span E (e '' s)) :
    ∃ l : Fin r → E, (∀ k, k ∉ s → l k = 0) ∧ x = ∑ k, l k • e k := by
  rw [Finsupp.mem_span_image_iff_linearCombination] at hx
  obtain ⟨l, hl, rfl⟩ := hx
  refine ⟨l, fun k hk => ?_, ?_⟩
  · by_contra h; exact hk (hl (Finsupp.mem_support_iff.mpr h))
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]; intro i; simp

theorem z_mem_orth (F : FlagG S r T) : F.z ∈ orth S (Submodule.span E (Set.range F.e)) := by
  unfold orth
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨a, rfl⟩ := hy; exact F.z_orth a
  | zero => simp
  | add a b _ _ ha hb => simp [map_add (f := _), ha, hb]
  | smul c a _ ha => simp [ha]

theorem exists_upUni (F : LFlag S r T) (n : S.V ≃ₗ[E] S.V)
    (h1 : ∀ j, ∀ x ∈ Xflag F (j + 1), n x - x ∈ Xflag F j)
    (h2 : ∀ x ∈ orth S (Xsp F), n x - x ∈ Xsp F) :
    ∃ W : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ a b, b < a → W a b = 0) ∧ (∀ a, W a a = 1) ∧
      ∀ b, n (frame F b) = ∑ a, W a b • frame F a := by
  have key : ∀ b : Fin (r + 1), ∃ l : Fin r → E, (∀ k, b ≤ Fin.castSucc k → l k = 0) ∧
      n (frame F b) = frame F b + ∑ k, l k • F.fl.e k := by
    intro b
    induction b using Fin.lastCases with
    | last =>
      have hz : frame F (Fin.last r) = F.fl.z := by simp [frame, FlagG.fvec]
      have hm := h2 _ (z_mem_orth F.fl)
      have hm' : n F.fl.z - F.fl.z ∈ Submodule.span E (F.fl.e '' Set.univ) := by
        rw [Set.image_univ]; exact hm
      obtain ⟨l, -, hl⟩ := exists_coef_of_mem_span_image F.fl.e Set.univ hm'
      refine ⟨l, fun k hk => absurd hk (not_le.mpr (Fin.castSucc_lt_last k)), ?_⟩
      rw [hz, ← hl]; abel
    | cast i =>
      have hf : frame F (Fin.castSucc i) = F.fl.e i := by simp [frame, FlagG.fvec]
      have hmem : F.fl.e i ∈ Xflag F (i.val + 1) :=
        Submodule.subset_span (Set.mem_image_of_mem _ (show i ∈ {k : Fin r | k.1 < i.1 + 1} from Nat.lt_succ_self _))
      have hm : n (F.fl.e i) - F.fl.e i ∈ Submodule.span E (F.fl.e '' {k : Fin r | k.1 < i.1}) := by
        have := h1 i.val _ hmem
        rw [hf] at *
        exact this
      obtain ⟨l, hl0, hl⟩ := exists_coef_of_mem_span_image F.fl.e _ hm
      refine ⟨l, fun k hk => hl0 k ?_, ?_⟩
      · simp only [Set.mem_setOf_eq, not_lt]; exact Fin.castSucc_le_castSucc_iff.mp hk
      · rw [hf, ← hl]; abel
  choose l hl0 hl using key
  refine ⟨Matrix.of fun a b => Fin.snoc (α := fun _ => E) (l b) 0 a + if a = b then 1 else 0, ?_, ?_, ?_⟩
  · intro a b hab
    simp only [Matrix.of_apply, if_neg (ne_of_gt hab), add_zero]
    induction a using Fin.lastCases with
    | last => simp
    | cast k => simp only [Fin.snoc_castSucc]; exact hl0 b k hab.le
  · intro a
    simp only [Matrix.of_apply, if_pos rfl]
    induction a using Fin.lastCases with
    | last => simp
    | cast k => simp only [Fin.snoc_castSucc]; rw [hl0 _ k le_rfl]; simp
  · intro b
    rw [hl b]
    simp only [Matrix.of_apply, add_smul, Finset.sum_add_distrib, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Fin.sum_univ_castSucc]
    simp [frame, FlagG.fvec, add_comm]

theorem upUni_mul {N : ℕ} {U W : Matrix (Fin N) (Fin N) E} (hU0 : ∀ a b, b < a → U a b = 0)
    (hU1 : ∀ a, U a a = 1) (hW0 : ∀ a b, b < a → W a b = 0) (hW1 : ∀ a, W a a = 1) :
    (∀ a b, b < a → (U * W) a b = 0) ∧ (∀ a, (U * W) a a = 1) := by
  first
  | exact @_root_.GlobalTheory.UpperUnitriangularMul.upperUnitriangular_mul
  | exact _root_.GlobalTheory.UpperUnitriangularMul.upperUnitriangular_mul
  | (apply _root_.GlobalTheory.UpperUnitriangularMul.upperUnitriangular_mul <;> assumption)
  | (intros; apply _root_.GlobalTheory.UpperUnitriangularMul.upperUnitriangular_mul <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UpperUnitriangularMul.upperUnitriangular_mul <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UpperUnitriangularMul.upperUnitriangular_mul ..)

theorem frame_mapLF (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) (b : Fin (r + 1)) :
    frame (mapLF γ F) b = γ (frame F b) := by
  unfold mapLF
  rw [dite_eq_left hγ]
  induction b using Fin.lastCases with
  | last => simp [frame, FlagG.fvec, mapFlag]
  | cast k => simp [frame, FlagG.fvec, mapFlag]

end Gen

end GlobalTheory.MovedFrames

namespace GlobalTheory.MovedFrames

theorem map_sum_frame {E V : Type*} [Field E] [AddCommGroup V] [Module E V] {N : ℕ} (ρ : V ≃ₗ[E] V)
    (U W : Matrix (Fin N) (Fin N) E) (f g : Fin N → V) (hF : ∀ a, ρ (f a) = ∑ c, U c a • g c) (b : Fin N) :
    ρ (∑ a, W a b • f a) = ∑ c, (U * W) c b • g c := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_smul, hF, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => by rw [mul_comm]

end GlobalTheory.MovedFrames

namespace GlobalTheory.MovedFrames

theorem moved_frames : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (t₀ : TauC Y u u') (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ n m, n ∈ NRat (lf D (X.Fu u)) → m ∈ NRat (lf D (X.Fu u')) → ∃ B B' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, (∀ a b, b < a → B a b = 0) ∧ (∀ a, B a a = 1) ∧ (∀ a b, b < a → B' a b = 0) ∧ (∀ a, B' a a = 1) ∧ ∀ b, ρ (n (frame (lf D (X.Fu u)) b)) = ∑ a, B a b • frame F00 a ∧ ρ (n (frame (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))) b)) = ∑ a, B' a b • frame F'0 a := by
  intro D X Y u u' F00 F'0 t₀ ρ U U' hM n m hn hm
  obtain ⟨_, hU, hU', hF, hF'⟩ := hM
  obtain ⟨W, hW0, hW1, hWe⟩ := exists_upUni _ n hn.2.1 hn.2.2
  obtain ⟨W', hW'0, hW'1, hW'e⟩ := exists_upUni _ m hm.2.1 hm.2.2
  have hlin : t₀.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t₀.rep.2.2.1
  have hγ : n⁻¹ * t₀.lin * m ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := mul_mem (mul_mem (inv_mem hn.1) hlin) hm.1
  obtain ⟨hB0, hB1⟩ := upUni_mul (fun a b h => (hU a b).1 h) (fun a => (hU a a).2 rfl) hW0 hW1
  obtain ⟨hB'0, hB'1⟩ := upUni_mul (fun a b h => (hU' a b).1 h) (fun a => (hU' a a).2 rfl) hW'0 hW'1
  refine ⟨U * W, U' * W', hB0, hB1, hB'0, hB'1, fun b => ⟨?_, ?_⟩⟩
  · rw [hWe]
    exact map_sum_frame ρ U W _ _ hF b
  · have ht : ∀ a, t₀.lin (frame (lf D (X.Fu u')) a) = frame t₀.frame a := fun a => by
      rw [← frame_mapLF _ hlin]; rfl
    have hx : ∀ x, n ((n⁻¹ * t₀.lin * m) x) = t₀.lin (m x) := fun x => by
      rw [← LinearEquiv.mul_apply, show n * (n⁻¹ * t₀.lin * m) = t₀.lin * m by group,
        LinearEquiv.mul_apply]
    have hF2 : ∀ a, (t₀.lin.trans ρ) (frame (lf D (X.Fu u')) a) = ∑ c, U' c a • frame F'0 c := by
      intro a
      rw [LinearEquiv.trans_apply, ht, hF']
    rw [frame_mapLF _ hγ, hx, hW'e]
    have := map_sum_frame (t₀.lin.trans ρ) U' W' _ _ hF2 b
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← this, LinearEquiv.trans_apply, map_sum]

end GlobalTheory.MovedFrames
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovesToGivesIntegralMatricesStatement
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moves_to_gives_integral_matrices : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (t₀ : TauC Y u u') (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ n m, n ∈ NRat (lf D (X.Fu u)) → m ∈ NRat (lf D (X.Fu u')) → ∃ B B' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, (∀ a b, b < a → B a b = 0) ∧ (∀ a, B a a = 1) ∧ (∀ a b, b < a → B' a b = 0) ∧ (∀ a, B' a a = 1) ∧ ∀ b, ρ (n (frame (lf D (X.Fu u)) b)) = ∑ a, B a b • frame F00 a ∧ ρ (n (frame (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))) b)) = ∑ a, B' a b • frame F'0 a := by
  first | exact @GlobalTheory.MovedFrames.moved_frames | exact GlobalTheory.MovedFrames.moved_frames | (intros; apply GlobalTheory.MovedFrames.moved_frames <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalScalarEqOneAtPlaceOverTypePrimes
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalScalarEqOneAtPlaceOverTypePrimes
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HL

theorem GCoord.c_eq_one_of_gS_mem : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) {T T' : D.host.E} (F00 : LFlag (D.sp.Y 0) D.R.rS T) (F'0 : LFlag (D.sp.Y 0) D.R.rS T') (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS) (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G) (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)), ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → G.c (below D P) = 1 := by
  intro D X Y T T' F00 F'0 FP G c P hP
  set p : PlF D := below D P with hp
  have hmem : ∀ n : ℕ, ((n : 𝓞 D.host.F) ∈ p.asIdeal ↔ ((n : 𝓞 D.host.E)) ∈ P.asIdeal) := by
    intro n
    show (n : 𝓞 D.host.F) ∈ Ideal.comap _ P.asIdeal ↔ _
    rw [Ideal.mem_comap, map_natCast]
  have hg : ∃ i, ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal := by
    have h1 : ((gS D : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal := (hmem _).2 hP
    simp only [gS, Nat.cast_mul] at h1
    rcases p.isPrime.mem_or_mem h1 with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨i, hi⟩ := hg
  have hchar : Loc.resChar p = D.host.g i := by
    have hz : ((D.host.g i : ℕ) : 𝓞 D.host.F ⧸ p.asIdeal) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk p.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
      exact hi
    have hd : ringChar (𝓞 D.host.F ⧸ p.asIdeal) ∣ D.host.g i := ringChar.dvd hz
    exact (Nat.prime_dvd_prime_iff_eq (D.s.atP p).ellPrime.out (D.host.g_prime i)).1 hd
  have hgp : gpart p = D.host.g i := by
    have hne := D.host.g_ne
    fin_cases i
    · simp [gpart, hchar]
    · simp [gpart, hchar, Ne.symm hne]
  have hδ := Y.δ_pin p i hi
  have hne : ∀ j, ((D.host.g j : ℕ) : D.host.E) ≠ 0 := fun j => Nat.cast_ne_zero.2 (D.host.g_prime j).ne_zero
  have hneF : ∀ j, ((D.host.g j : ℕ) : D.host.F) ≠ 0 := fun j => Nat.cast_ne_zero.2 (D.host.g_prime j).ne_zero
  have key := c.c_eq p
  have hone : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((G.c p).val) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep 1 := by
    rw [key]
    change algebraMap _ _ (Y.δ p) * _ = _
    rw [hδ, ← (D.s.atP p).compat, ← map_mul, map_one]
    have h1 : algebraMap D.host.F D.host.E ((D.host.g 0 : D.host.F) * D.host.g 1 / D.host.g i) *
        ((uP p : ℚ) : D.host.E) = 1 := by
      simp only [uP, hgp, gS, map_div₀, map_mul, map_natCast]
      push_cast
      have := hne 0; have := hne 1; have := hne i
      field_simp
    rw [h1, map_one]
  haveI : Nontrivial (D.s.atP p).Ep :=
    Module.nontrivial_of_finrank_pos (R := (D.s.atP p).Fp) (by rw [(D.s.atP p).rank]; norm_num)
  have hv : ((G.c p).val : (D.s.atP p).Fp) = 1 :=
    (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep).injective hone
  exact Units.ext hv

end GlobalTheory.HL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalScalarEqOneAtPlaceOverTypePrimesStatement
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localScalar_eq_one_at_place_over_typePrimes : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) {T T' : D.host.E} (F00 : LFlag (D.sp.Y 0) D.R.rS T) (F'0 : LFlag (D.sp.Y 0) D.R.rS T') (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS) (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G) (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)), ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → G.c (below D P) = 1 := by
  first | exact @GlobalTheory.HL.GCoord.c_eq_one_of_gS_mem | exact GlobalTheory.HL.GCoord.c_eq_one_of_gS_mem | (intros; apply GlobalTheory.HL.GCoord.c_eq_one_of_gS_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ThetaSmulCompletedLatticeIffTypePrimeMul
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ThetaSmulCompletedLatticeIffTypePrimeMul
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HL.ThetaG

open IsDedekindDomain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}

theorem mem_lat_span_smul_iff (A : Places F E sig) {n : ℕ} (p : HeightOneSpectrum (𝓞 F))
    (Λ : Submodule (𝓞 E) (Fin n → E)) (a : 𝓞 E) (x : Fin n → (A.loc p).Ep) :
    x ∈ A.lat p (Ideal.span {a} • Λ) ↔ ∃ z ∈ A.lat p Λ, x = (A.loc p).ιE (a : E) • z := by
  let φ : (Fin n → (A.loc p).Ep) →ₗ[(A.L p).O] (Fin n → (A.loc p).Ep) :=
    (LinearMap.lsmul (A.loc p).Ep (Fin n → (A.loc p).Ep) ((A.loc p).ιE (a : E))).restrictScalars (A.L p).O
  have hφ : ∀ v, φ v = (A.loc p).ιE (a : E) • v := fun v => rfl
  have hbc : ∀ v : Fin n → E, A.bc p (a • v) = φ (A.bc p v) := by
    intro v
    funext i
    show (A.loc p).ιE ((a : E) * v i) = (A.loc p).ιE (a : E) * (A.loc p).ιE (v i)
    exact map_mul _ _ _
  have hset : A.bc p '' ((Ideal.span {a} • Λ : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) =
      φ '' (A.bc p '' (Λ : Set (Fin n → E))) := by
    rw [Submodule.ideal_span_singleton_smul, Submodule.coe_pointwise_smul, ← Set.image_smul,
      Set.image_image, Set.image_image]
    exact Set.image_congr fun v _ => hbc v
  have heq : A.lat p (Ideal.span {a} • Λ) = (A.lat p Λ).map φ := by
    unfold Places.lat
    rw [hset, Submodule.map_span]
  rw [heq, Submodule.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, rfl⟩

theorem smul_mem_iff_of_unit {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (O : Subring R)
    (N : Submodule O M) (θ s w b : R) (hw : w ∈ O) (hb : b ∈ O) (hs : s = θ * b) (hwb : w * b = 1) (x : M) :
    (∃ y ∈ N, x = θ • y) ↔ ∃ z ∈ N, x = s • z := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(⟨w, hw⟩ : O) • y, N.smul_mem _ hy, ?_⟩
    rw [Subring.smul_def, smul_smul, hs, mul_assoc, mul_comm b w, hwb, mul_one]
  · rintro ⟨z, hz, rfl⟩
    refine ⟨(⟨b, hb⟩ : O) • z, N.smul_mem _ hz, ?_⟩
    rw [Subring.smul_def, smul_smul, hs]

theorem resChar_eq_of_mem (p : HeightOneSpectrum (𝓞 F)) {q : ℕ} (hq : q.Prime)
    (h : ((q : ℕ) : 𝓞 F) ∈ p.asIdeal) : Formalism.MainNotions.S.Loc.resChar p = q := by
  unfold Formalism.MainNotions.S.Loc.resChar
  haveI := p.isPrime
  have h0 : ((q : ℕ) : 𝓞 F ⧸ p.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk p.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 h
  rcases hq.eq_one_or_self_of_dvd _ (ringChar.dvd h0) with h1 | h1
  · exact absurd h1 CharP.ringChar_ne_one
  · exact h1

end GlobalTheory.HL.ThetaG

namespace GlobalTheory.HL.ThetaG

open IsDedekindDomain ValuativeRel

theorem inTh_lat_iff : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) {T T' : D.host.E} (F00 : LFlag (D.sp.Y 0) D.R.rS T) (F'0 : LFlag (D.sp.Y 0) D.R.rS T') (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS) (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G) (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)), ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ∀ (Λ : G.Lt) (x : (G.S (below D P)).V), (G.S (below D P)).InTh ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat (below D P) Λ) x ↔ x ∈ (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat (below D P) (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ) := by
  intro D X Y T T' F00 F'0 FP G c P hP Λ x
  haveI := P.isPrime
  have hmem : ∀ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal →
      Formalism.MainNotions.S.Loc.resChar (below D P) = D.host.g i := by
    intro i hi
    apply resChar_eq_of_mem (below D P) (D.host.g_prime i)
    change _ ∈ Ideal.comap _ P.asIdeal
    rw [Ideal.mem_comap, map_natCast]
    exact hi
  have hg : ((gS D : ℕ) : 𝓞 D.host.E) =
      ((D.host.g 0 : ℕ) : 𝓞 D.host.E) * ((D.host.g 1 : ℕ) : 𝓞 D.host.E) := by
    unfold gS
    push_cast
    ring
  obtain ⟨i, j, hij, hi, hgij⟩ : ∃ i j : Fin 2, D.host.g i ≠ D.host.g j ∧
      ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal ∧
      ((gS D : ℕ) : 𝓞 D.host.E) = ((D.host.g i : ℕ) : 𝓞 D.host.E) * ((D.host.g j : ℕ) : 𝓞 D.host.E) := by
    rw [hg] at hP
    rcases P.isPrime.mem_or_mem hP with h | h
    · exact ⟨0, 1, D.host.g_ne, h, hg⟩
    · exact ⟨1, 0, D.host.g_ne.symm, h, by rw [hg, mul_comm]⟩
  have hres := hmem i hi
  have hj : ((D.host.g j : ℕ) : 𝓞 D.host.F) ∉ (below D P).asIdeal := by
    intro hj'
    exact hij (hres.symm.trans (resChar_eq_of_mem (below D P) (D.host.g_prime j) hj'))
  have hsome : ((D.s.atP (below D P)).split).isSome = true :=
    (D.s_split (below D P)).2 (by rw [hres]; fin_cases i <;> simp)
  obtain ⟨sg, hsg⟩ := Option.isSome_iff_exists.1 hsome
  have hA := (Y.agree (below D P)).2.2.2.2.2
  rw [hsg] at hA
  obtain ⟨g', hM, hq⟩ : ∃ g', (Y.M (below D P)).split = some g' ∧ g'.q = sg.q := by
    cases hM : (Y.M (below D P)).split with
    | none => rw [hM] at hA; exact hA.elim
    | some g' => rw [hM] at hA; exact ⟨g', rfl, hA.2⟩
  have hgg := (c.c (below D P)).gg_some g' hM
  have hth : (G.S (below D P)).th = ((D.host.g i : ℕ) : (D.s.atP (below D P)).Fp) := by
    unfold Frames.th
    rw [if_pos hgg.1, hgg.2, hq, sg.q_eq, hres]
  haveI := ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).char0
  have hgj0 : ((D.host.g j : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp) ≠ 0 :=
    Nat.cast_ne_zero.2 (D.host.g_prime j).ne_zero
  have hval : (below D P).valuation D.host.F ((D.host.g j : ℕ) : D.host.F) = 1 := by
    rw [← map_natCast (algebraMap (𝓞 D.host.F) D.host.F)]
    exact le_antisymm ((below D P).valuation_le_one _)
      (not_lt.1 fun hlt => hj (((below D P).valuation_lt_one_iff_mem (K := D.host.F) _).1 hlt))
  have hint : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).ιF ((D.host.g j : ℕ) : D.host.F)⁻¹ ∈ 𝒪[((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp] :=
    (GlobalTheory.HL.PlacesInt.mem_int_iff ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)) _).2 (by rw [map_inv₀, hval, inv_one])
  have hιF : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).ιF ((D.host.g j : ℕ) : D.host.F)⁻¹ =
      ((D.host.g j : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp)⁻¹ := by
    rw [map_inv₀, map_natCast]
  let w : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep :=
    algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep ((D.host.g j : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp)⁻¹
  have hwO : w ∈ ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).L (below D P)).O := by
    rw [hιF] at hint
    refine (((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).L (below D P)).O_def _).2 ?_
    have : IsIntegral 𝒪[((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp]
        (algebraMap 𝒪[((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp] ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep ⟨_, hint⟩) :=
      isIntegral_algebraMap
    exact this
  have hw : w * ((D.host.g j : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep) = 1 := by
    simp only [w]
    rw [← map_natCast (algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep), ← map_mul,
      inv_mul_cancel₀ hgj0, map_one]
  have huO : ((D.host.g j : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep) ∈
      ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).L (below D P)).O :=
    natCast_mem _ _
  have hι : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).ιE (((((D.host.g i : ℕ) : 𝓞 D.host.E) * ((D.host.g j : ℕ) : 𝓞 D.host.E) :
      𝓞 D.host.E)) : D.host.E) =
      ((D.host.g i : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep) * ((D.host.g j : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep) := by
    push_cast
    rw [map_mul, map_natCast, map_natCast]
  have hθE : algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp
      ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep (G.S (below D P)).th =
      ((D.host.g i : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep) := by
    rw [hth]
    exact map_natCast _ _
  have hιS : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).ιE ((((gS D : ℕ) : 𝓞 D.host.E)) : D.host.E) =
      ((D.host.g i : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep) *
        ((D.host.g j : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep) := by
    rw [hgij]
    exact hι
  obtain ⟨a, ha⟩ : ∃ a : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep, ((D.host.g i : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep) = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep, ((D.host.g j : ℕ) : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep) = b := ⟨_, rfl⟩
  rw [ha, hb] at hιS
  rw [ha] at hθE
  rw [hb] at hw huO
  clear_value w
  have hs : ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).ιE ((((gS D : ℕ) : 𝓞 D.host.E)) : D.host.E) =
      algebraMap ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Fp
        ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).Ep (G.S (below D P)).th * b := by
    rw [hιS, hθE]
  unfold Frames.InTh
  rw [mem_lat_span_smul_iff]
  exact smul_mem_iff_of_unit _ _ _ _ w b hwO huO hs hw x

end GlobalTheory.HL.ThetaG
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ThetaSmulCompletedLatticeIffTypePrimeMulStatement
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_smul_completedLattice_iff_typePrimeMul : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) {T T' : D.host.E} (F00 : LFlag (D.sp.Y 0) D.R.rS T) (F'0 : LFlag (D.sp.Y 0) D.R.rS T') (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS) (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G) (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)), ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ∀ (Λ : G.Lt) (x : (G.S (below D P)).V), (G.S (below D P)).InTh ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat (below D P) Λ) x ↔ x ∈ (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat (below D P) (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ) := by
  first | exact @GlobalTheory.HL.ThetaG.inTh_lat_iff | exact GlobalTheory.HL.ThetaG.inTh_lat_iff | (intros; apply GlobalTheory.HL.ThetaG.inTh_lat_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedFrameMemRowLatticesOfWord
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedFrameMemRowLatticesOfWord
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowFrame

theorem ddIdeal_ne_bot (D : D7) :
    (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)) : Ideal (𝓞 D.host.E)) ≠ ⊥ :=
  Ideal.map_ne_bot_of_ne_bot differentIdeal_ne_bot

theorem one_mem_ddS_zpow_neg (D : D7) (m : ℕ) :
    (1 : D.host.E) ∈ (ddS D ^ (-(m : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
  rw [zpow_neg, zpow_natCast, ddS, ← FractionalIdeal.coeIdeal_pow]
  refine FractionalIdeal.one_mem_inv_coe_ideal ?_
  rw [← Ideal.zero_eq_bot]
  exact pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact ddIdeal_ne_bot D)

theorem frame_mem_rowLat (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : IsRowLat D F0 Λ) (a : Fin (D.R.rS + 1)) :
    frame (lf D F0) a ∈ Λ := by
  obtain ⟨-, ⟨-, -, hz, -⟩, hX⟩ := hΛ
  have hXS : XS D F0 ≤ Λ := by
    rw [← hX]; exact inf_le_left
  induction a using Fin.lastCases with
  | last =>
    show Fin.snoc (α := fun _ => (VS D).V) F0.e F0.z (Fin.last _) ∈ Λ
    rw [Fin.snoc_last]; exact hz.1
  | cast i =>
    show Fin.snoc (α := fun _ => (VS D).V) F0.e F0.z i.castSucc ∈ Λ
    rw [Fin.snoc_castSucc]
    apply hXS
    apply Submodule.subset_span
    refine ⟨i, 1, ?_, (one_smul _ _).symm⟩
    have : -((D.R.rS : ℤ) - ((i : ℕ) : ℤ)) = -(((D.R.rS - (i : ℕ) : ℕ)) : ℤ) := by
      rw [Nat.cast_sub i.isLt.le]
    rw [this]
    exact one_mem_ddS_zpow_neg D _

theorem frame_mem_rows : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    Λ ∈ Y.what₂ u → ∀ a, frame (lf D (X.Fu u)) a ∈ Λ :=
  fun D X Y u Λ hΛ a => frame_mem_rowLat D (X.Fu u) Λ ((Y.rowsOK u).1 Λ hΛ) a

end GlobalTheory.RowFrame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedFrameMemRowLatticesOfWordStatement
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixedFrame_mem_rowLattices_of_word : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (Λ : Submodule (𝓞 D.host.E) (VS D).V), Λ ∈ Y.what₂ u → ∀ a, frame (lf D (X.Fu u)) a ∈ Λ := by
  first | exact @GlobalTheory.RowFrame.frame_mem_rows | exact GlobalTheory.RowFrame.frame_mem_rows | (intros; apply GlobalTheory.RowFrame.frame_mem_rows <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermFramesCongrModThetaUnitriangular
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermFramesCongrModThetaUnitriangular
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.FrameChange

theorem coef_zero {ι M R : Type*} [CommRing R] [AddCommGroup M] [Module R M] {v : ι → M}
    (hv : LinearIndependent R v) {s : Set ι} {x : ι} (hx : x ∉ s) {c : R}
    (h : c • v x ∈ Submodule.span R (v '' s)) : c = 0 := by
  rw [Finsupp.mem_span_image_iff_linearCombination] at h
  obtain ⟨l, hl, e⟩ := h
  have h2 : Finsupp.single x c = l := hv (by rw [e, Finsupp.linearCombination_single])
  have h3 := congrArg (fun l : ι →₀ R => l x) h2
  simp only [Finsupp.single_eq_same] at h3
  rw [h3]
  exact (Finsupp.mem_supported' _ _).1 hl x hx

theorem diag_mul {m : ℕ} {R : Type*} [CommRing R] {P Q : Matrix (Fin m) (Fin m) R}
    (hP : P.BlockTriangular id) (hQ : Q.BlockTriangular id) (a : Fin m) :
    (P * Q) a a = P a a * Q a a := by
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · intro c _ hc
    rcases lt_or_gt_of_ne hc with h | h
    · rw [hP h, zero_mul]
    · rw [hQ h, mul_zero]
  · intro h; exact absurd (Finset.mem_univ a) h

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem sum_mem_spanTo (g g' : Fin (r + 1) → S.V) (hg' : ∀ a : Fin (r + 1), g' a ∈ S.spanTo g (a + 1))
    (c : Fin (r + 1) → E) (j : ℕ) (hc : ∀ a : Fin (r + 1), j ≤ (a : ℕ) → c a = 0) :
    ∑ a, c a • g' a ∈ S.spanTo g j :=
  Submodule.sum_mem _ fun a _ => by
    by_cases h : (a : ℕ) < j
    · exact Submodule.smul_mem _ _ (TermBasic.spanTo_mono S g (by omega) (hg' a))
    · rw [hc a (by omega), zero_smul]; exact Submodule.zero_mem _

theorem coeffs (g : Fin (r + 1) → S.V) (j : ℕ) (v : S.V)
    (hv : v ∈ Submodule.span L.O (g '' {i | (i : ℕ) < j})) :
    ∃ c : Fin (r + 1) → L.O, (∀ a : Fin (r + 1), j ≤ (a : ℕ) → c a = 0) ∧
      v = ∑ a, ((c a : L.O) : E) • g a := by
  rw [Finsupp.mem_span_image_iff_linearCombination] at hv
  obtain ⟨l, hl, rfl⟩ := hv
  refine ⟨l, fun a ha => (Finsupp.mem_supported' _ _).1 hl a (by simp; omega), ?_⟩
  rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]
  rfl

end GlobalTheory.HL.FrameChange

namespace GlobalTheory.HL.FrameChange

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem tri_coeffs {g : Fin (r + 1) → S.V} (hg : ∀ a (j : Fin r), hf L S.Hm (g a) (g j.castSucc) = 0)
    (hli : LinearIndependent E g) {n : S.GLV} (hn : n ∈ S.Nof g) {Λ : Submodule L.O S.V}
    (t : ∀ j ≤ r + 1, ∀ x, (x ∈ Λ ∧ x ∈ S.spanTo g j) ↔
      x ∈ Submodule.span L.O ((fun b => n (g b)) '' {i | (i : ℕ) < j}))
    (z : Fin (r + 1) → S.V) (B : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hB0 : ∀ a b, b < a → B a b = 0) (hB1 : ∀ a, B a a = 1) (hz : ∀ b, z b = ∑ a, B a b • g a)
    (hzΛ : ∀ b, z b ∈ Λ) :
    ∃ C : Matrix (Fin (r + 1)) (Fin (r + 1)) L.O, (∀ a b, b < a → C a b = 0) ∧ (∀ a, C a a = 1) ∧
      ∀ b, z b = ∑ a, ((C a b : L.O) : E) • n (g a) := by
  have hself : ∀ a : Fin (r + 1), g a ∈ S.spanTo g (a + 1) := fun a =>
    TermBasic.self_mem S g (by omega)
  have hmem : ∀ a : Fin (r + 1), n (g a) ∈ S.spanTo g (a + 1) := fun a =>
    TermBasic.map_mem hg hn _ (hself a)
  have key : ∀ b : Fin (r + 1), ∃ c : Fin (r + 1) → L.O, (∀ a : Fin (r + 1), (b : ℕ) + 1 ≤ (a : ℕ) → c a = 0) ∧
      z b = ∑ a, ((c a : L.O) : E) • n (g a) := fun b => by
    have h1 : z b ∈ S.spanTo g (b + 1) := by
      rw [hz b]
      exact sum_mem_spanTo S g g hself _ _ fun a ha => hB0 a b (Fin.lt_def.2 (by omega))
    exact coeffs S _ _ _ ((t _ (by omega) _).1 ⟨hzΛ b, h1⟩)
  choose c hc0 hc using key
  refine ⟨Matrix.of fun a b => c b a, fun a b h => hc0 b a (by rw [Fin.lt_def] at h; omega),
    fun b => ?_, fun b => hc b⟩
  show c b b = 1
  apply Subtype.ext
  have e1 : z b - g b ∈ S.spanTo g b := by
    have : z b - g b = ∑ a, (B a b - if a = b then 1 else 0) • g a := by
      rw [hz b]; simp [sub_smul, Finset.sum_sub_distrib, ite_smul]
    rw [this]
    refine sum_mem_spanTo S g g hself _ _ fun a ha => ?_
    by_cases hab : a = b
    · subst hab; simp [hB1]
    · have : b < a := Fin.lt_def.2 (by have := Fin.val_ne_of_ne hab; omega)
      simp [hab, hB0 a b this]
  have e2 : z b - ((c b b : L.O) : E) • n (g b) ∈ S.spanTo g b := by
    have : z b - ((c b b : L.O) : E) • n (g b) =
        ∑ a, (((c b a : L.O) : E) - if a = b then ((c b b : L.O) : E) else 0) • n (g a) := by
      rw [hc b]; simp [sub_smul, Finset.sum_sub_distrib, ite_smul]
    rw [this]
    refine sum_mem_spanTo S g _ hmem _ _ fun a ha => ?_
    by_cases hab : a = b
    · subst hab; simp
    · have := Fin.val_ne_of_ne hab
      simp [hab, hc0 b a (by omega)]
  have e3 : n (g b) - g b ∈ S.spanTo g b := TermBasic.sub_mem hg hn b
  have e4 : (((c b b : L.O) : E) - 1) • g b = (z b - g b) - (z b - ((c b b : L.O) : E) • n (g b)) -
      ((c b b : L.O) : E) • (n (g b) - g b) := by
    simp only [sub_smul, smul_sub, one_smul]; abel
  have h5 := (S.spanTo g b).sub_mem ((S.spanTo g b).sub_mem e1 e2) ((S.spanTo g b).smul_mem ((c b b : L.O) : E) e3)
  rw [← e4] at h5
  have h6 := coef_zero hli (s := {i | (i : ℕ) < b}) (x := b) (by simp) h5
  simpa [sub_eq_zero] using h6

end GlobalTheory.HL.FrameChange

namespace GlobalTheory.HL.FrameChange

theorem frames_congr : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : Formalism.MainNotions.S.Loc.LocE F E) (r k : ℕ) (S : GlobalTheory.HL.Frames L r k) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → ∀ (y x : Fin (r + 1) → S.V) (B B' : Matrix (Fin (r + 1)) (Fin (r + 1)) E), (∀ a b, b < a → B a b = 0) → (∀ a, B a a = 1) → (∀ a b, b < a → B' a b = 0) → (∀ a, B' a a = 1) → (∀ b, y b = ∑ a, B a b • S.f a) → (∀ b, x b = ∑ a, B' a b • S.f' a) → (∀ a, y a ∈ Λ) → (∀ b, x b ∈ Λ) → ∃ ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ a b, ξ a b ∈ L.O) ∧ (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ ∀ b, S.InTh Λ (x b - ∑ a, ξ a b • y a) := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT y x B B' hB0 hB1 hB'0 hB'1 hy hx hyΛ hxΛ
  obtain ⟨-, hW, -, t, t', hli, -, -⟩ := TermBasic.term_basic L r k S d Λ hT
  obtain ⟨-, -, hn, hn', -, -, hth, -⟩ := hW
  have hg : ∀ a (j : Fin r), hf L S.Hm (S.f a) (S.f j.castSucc) = 0 := fun a j => by
    simp [S.gram, Fin.castSucc_ne_last]
  have hg' : ∀ a (j : Fin r), hf L S.Hm (S.f' a) (S.f' j.castSucc) = 0 := fun a j => by
    simp [S.gram', Fin.castSucc_ne_last]
  have hl1 : LinearIndependent E (S.fr d Λ) := hli.comp Sum.inl Sum.inl_injective
  have hl2 : LinearIndependent E (S.fr' d Λ) := hli.comp Sum.inr Sum.inr_injective
  have hlf : LinearIndependent E S.f := by
    have := hl1.map' (S.wit d Λ).1.symm.toLinearMap (LinearEquiv.ker _)
    have e : S.f = ⇑((S.wit d Λ).1.symm.toLinearMap) ∘ S.fr d Λ := by
      funext a; simp [Frames.fr]
    rw [e]; exact this
  have hlf' : LinearIndependent E S.f' := by
    have := hl2.map' (S.wit d Λ).2.symm.toLinearMap (LinearEquiv.ker _)
    have e : S.f' = ⇑((S.wit d Λ).2.symm.toLinearMap) ∘ S.fr' d Λ := by
      funext a; simp [Frames.fr']
    rw [e]; exact this
  obtain ⟨C, hC0, hC1, hCy⟩ := tri_coeffs S hg hlf hn t y B hB0 hB1 hy hyΛ
  obtain ⟨C', hC'0, hC'1, hC'x⟩ := tri_coeffs S hg' hlf' hn' t' x B' hB'0 hB'1 hx hxΛ
  have hCt : C.BlockTriangular id := fun a b h => hC0 a b h
  have hC't : C'.BlockTriangular id := fun a b h => hC'0 a b h
  have hdet : C.det = 1 := by
    rw [Matrix.det_of_upperTriangular hCt]; simp [hC1]
  letI : Invertible C := Matrix.invertibleOfIsUnitDet C (by rw [hdet]; exact isUnit_one)
  have hCit : C⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hCt
  have hCi1 : ∀ a, C⁻¹ a a = 1 := fun a => by
    have h1 := diag_mul hCit hCt a
    rw [Matrix.inv_mul_of_invertible, hC1, mul_one] at h1
    simpa using h1.symm
  set D := C⁻¹ * C' with hD
  have hDt : D.BlockTriangular id := hCit.mul hC't
  have hCD : C * D = C' := by rw [hD, ← Matrix.mul_assoc, Matrix.mul_inv_of_invertible, Matrix.one_mul]
  choose w hwΛ hw using hth
  refine ⟨Matrix.of fun a b => ((D a b : L.O) : E), fun a b => (D a b).2, fun a b h => ?_, fun a => ?_,
    fun b => ?_⟩
  · simp [hDt h]
  · simp [hD, diag_mul hCit hC't, hCi1, hC'1]
  · have e1 : ∑ a, (Matrix.of fun a b => ((D a b : L.O) : E)) a b • y a =
        ∑ c, ((C' c b : L.O) : E) • (S.wit d Λ).1 (S.f c) := by
      simp only [Matrix.of_apply, hCy, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← Finset.sum_smul, ← hCD, Matrix.mul_apply]
      push_cast
      simp only [mul_comm]
    refine ⟨∑ c, ((C' c b : L.O) : E) • w c, Λ.sum_mem fun c _ => Λ.smul_mem (C' c b) (hwΛ c), ?_⟩
    rw [e1, hC'x b, ← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← smul_sub, hw c, smul_comm]

end GlobalTheory.HL.FrameChange
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermFramesCongrModThetaUnitriangularStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.term_frames_congr_mod_theta_unitriangular : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : Formalism.MainNotions.S.Loc.LocE F E) (r k : ℕ) (S : GlobalTheory.HL.Frames L r k) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → ∀ (y x : Fin (r + 1) → S.V) (B B' : Matrix (Fin (r + 1)) (Fin (r + 1)) E), (∀ a b, b < a → B a b = 0) → (∀ a, B a a = 1) → (∀ a b, b < a → B' a b = 0) → (∀ a, B' a a = 1) → (∀ b, y b = ∑ a, B a b • S.f a) → (∀ b, x b = ∑ a, B' a b • S.f' a) → (∀ a, y a ∈ Λ) → (∀ b, x b ∈ Λ) → ∃ ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ a b, ξ a b ∈ L.O) ∧ (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ ∀ b, S.InTh Λ (x b - ∑ a, ξ a b • y a) := by
  first | exact @GlobalTheory.HL.FrameChange.frames_congr | exact GlobalTheory.HL.FrameChange.frames_congr | (intros; apply GlobalTheory.HL.FrameChange.frames_congr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovedReferenceFrameCongruentUnitriangular
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HL.LocCong

theorem bc_sum {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
    (A : GlobalTheory.HL.Places F E sig) {N r : ℕ} (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (B : Fin (r + 1) → E) (v : Fin (r + 1) → Fin N → E) :
    A.bc p (∑ a, B a • v a) = ∑ a, (A.loc p).ιE (B a) • A.bc p (v a) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [GlobalTheory.HL.Places.bc, Finset.sum_apply, map_sum, smul_eq_mul]

theorem loc_cong : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ n m, n ∈ NRat (lf D (X.Fu u)) → m ∈ NRat (lf D (X.Fu u')) → Formalism.HermitianLatticesTheory.gmap (n⁻¹ * t₀.lin * m) t₀.lam' = t₀.lam → (∃ d, G.IsTerm d (c.lat (ρ * n) t₀.lam)) → ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E), ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ∃ ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E), (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ ∀ b, frame (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))) b - frameAct (frame (lf D (X.Fu u))) ξ b ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • t₀.lam)) := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hG hFP G c t₀ ρ U U' hMov n m hn hm hgm hterm P hP
  obtain ⟨d, hlat, hloc⟩ := hterm
  obtain ⟨B, B', hB1, hB2, hB1', hB2', hBB⟩ := GlobalTheory.T.moves_to_gives_integral_matrices D X Y u u' F00 F'0 t₀ ρ U U' hMov n m hn hm
  have hc1 := GlobalTheory.T.localScalar_eq_one_at_place_over_typePrimes D X Y F00 F'0 FP G c P hP
  have hSf : ∀ a, (G.S (below D P)).f a = (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).bc (below D P) (G.f a) := by
    intro a
    have := G.f_eq (below D P) a
    rw [hc1] at this
    simpa using this
  have hSf' : ∀ a, (G.S (below D P)).f' a = (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).bc (below D P) (G.f' a) := by
    intro a
    have := G.f'_eq (below D P) a
    rw [hc1] at this
    simpa using this
  have hiso : n⁻¹ * t₀.lin * m ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hn.1) t₀.rep.2.2.1) hm.1
  have hfr : ∀ b, frame (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))) b = (n⁻¹ * t₀.lin * m) (frame (lf D (X.Fu u')) b) := by
    intro b
    unfold mapLF
    rw [dite_eq_left hiso]
    simp only [frame, Formalism.MainNotions.S.FlagG.fvec, mapFlag]
    exact (congrFun (Fin.comp_snoc (⇑(n⁻¹ * t₀.lin * m)) _ _) b).symm
  have hyin : ∀ a, frame (lf D (X.Fu u)) a ∈ t₀.lam := fun a => GlobalTheory.T.fixedFrame_mem_rowLattices_of_word D X Y u t₀.lam t₀.mem a
  have hxin : ∀ b, frame (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))) b ∈ t₀.lam := by
    intro b
    rw [hfr b, ← hgm]
    exact Submodule.mem_map_of_mem (GlobalTheory.T.fixedFrame_mem_rowLattices_of_word D X Y u' t₀.lam' t₀.mem' b)
  have hy : ∀ b, c.e ((ρ * n) (frame (lf D (X.Fu u)) b)) = ∑ a, B a b • G.f a := by
    intro b
    set_option synthInstance.maxHeartbeats 100000 in
      rw [LinearEquiv.mul_apply, (hBB b).1, map_sum]
    simp only [map_smul, c.f_eq]
  have hx : ∀ b, c.e ((ρ * n) (frame (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))) b)) = ∑ a, B' a b • G.f' a := by
    intro b
    set_option synthInstance.maxHeartbeats 100000 in
      rw [LinearEquiv.mul_apply, (hBB b).2, map_sum]
    simp only [map_smul, c.f'_eq]
  have hmemc : ∀ v ∈ t₀.lam, c.e ((ρ * n) v) ∈ c.lat (ρ * n) t₀.lam := fun v hv =>
    Submodule.mem_map.2 ⟨v, hv, rfl⟩
  haveI := ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).lf
  haveI := ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).char0
  obtain ⟨ξp, hξO, hξ1, hξ2, hξT⟩ := GlobalTheory.T.term_frames_congr_mod_theta_unitriangular _ D.R.rS D.R.k (G.S (below D P)) (d (below D P))
    ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat (below D P) (c.lat (ρ * n) t₀.lam)) (hloc (below D P))
    (fun b => (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).bc (below D P) (c.e ((ρ * n) (frame (lf D (X.Fu u)) b))))
    (fun b => (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).bc (below D P) (c.e ((ρ * n) (frame (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))) b))))
    (fun a b => ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).ιE (B a b)) (fun a b => ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).ιE (B' a b))
    (fun a b h => by simp [hB1 a b h]) (fun a => by simp [hB2 a])
    (fun a b h => by simp [hB1' a b h]) (fun a => by simp [hB2' a])
    (fun b => by simp only [hy, bc_sum, hSf])
    (fun b => by simp only [hx, bc_sum, hSf'])
    (fun a => Submodule.subset_span ⟨_, hmemc _ (hyin a), rfl⟩)
    (fun b => Submodule.subset_span ⟨_, hmemc _ (hxin b), rfl⟩)
  have hfg : (c.lat (ρ * n) t₀.lam).FG := hlat.fg
  have hpos : 0 < gS D := by
    unfold gS
    exact Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  obtain ⟨ξ, hu1, hu2, hPP⟩ := GlobalTheory.T.exists_global_unitriangular_of_local_congruence (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) _ D.R.rS (c.lat (ρ * n) t₀.lam) hfg
    (gS D) hpos (below D P)
    (fun b => c.e ((ρ * n) (frame (lf D (X.Fu u)) b)))
    (fun b => c.e ((ρ * n) (frame (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))) b))) ξp hξO hξ1 hξ2
    (fun a => Submodule.subset_span ⟨_, hmemc _ (hyin a), rfl⟩)
    (fun b => (GlobalTheory.T.theta_smul_completedLattice_iff_typePrimeMul D X Y F00 F'0 FP G c P hP (c.lat (ρ * n) t₀.lam) _).1 (hξT b))
  refine ⟨ξ, hu1, hu2, fun b => ?_⟩
  have h := hPP P rfl b
  set v := frame (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))) b - frameAct (frame (lf D (X.Fu u))) ξ b with hv
  have hφ : c.e ((ρ * n) (frame (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))) b)) -
      ∑ a, ((ξ a b : 𝓞 D.host.E) : D.host.E) • c.e ((ρ * n) (frame (lf D (X.Fu u)) a)) = c.e ((ρ * n) v) := by
    rw [hv, map_sub, map_sub]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [frameAct, map_sum, map_smul]
  rw [hφ] at h
  have hmap : Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • c.lat (ρ * n) t₀.lam =
      (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • t₀.lam).map
        ((((ρ * n).trans c.e : (VS D).V ≃ₗ[D.host.E] G.V) : (VS D).V →ₗ[D.host.E] G.V).restrictScalars (𝓞 D.host.E)) := by
    unfold GCoord.lat
    rw [Submodule.map_smul'']
  rw [hmap] at h
  obtain ⟨s, hs, hsv⟩ := h
  refine ⟨s, hs, ?_⟩
  obtain ⟨z, hz, hzv⟩ := Submodule.mem_map.1 hsv
  have hinj : Function.Injective ((((ρ * n).trans c.e : (VS D).V ≃ₗ[D.host.E] G.V) : (VS D).V →ₗ[D.host.E] G.V).restrictScalars (𝓞 D.host.E)) :=
    ((ρ * n).trans c.e).injective
  have : z = s • v := by
    apply hinj
    rw [hzv, LinearMap.map_smul]
    rfl
  rw [← this]
  exact hz

end GlobalTheory.HL.LocCong
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovedReferenceFrameCongruentUnitriangularStatement
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedReferenceFrame_congruent_unitriangular : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ n m, n ∈ NRat (lf D (X.Fu u)) → m ∈ NRat (lf D (X.Fu u')) → Formalism.HermitianLatticesTheory.gmap (n⁻¹ * t₀.lin * m) t₀.lam' = t₀.lam → (∃ d, G.IsTerm d (c.lat (ρ * n) t₀.lam)) → ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E), ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ∃ ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E), (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ ∀ b, frame (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))) b - frameAct (frame (lf D (X.Fu u))) ξ b ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • t₀.lam)) := by
  first | exact @GlobalTheory.HL.LocCong.loc_cong | exact GlobalTheory.HL.LocCong.loc_cong | (intros; apply GlobalTheory.HL.LocCong.loc_cong <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdmissibleIntegralFrameOfLocalTerms
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.AdmFrame

theorem frame_mem_locP (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hL : IsLift Λ (lf D F0)) (hF : FrameOK D Λ (lf D F0))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal)
    (a : Fin (D.R.rS + 1)) : frame (lf D F0) a ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ) := by
  haveI := P.isPrime
  induction a using Fin.lastCases with
  | last =>
    refine ⟨1, P.asIdeal.primeCompl.one_mem, ?_⟩
    simp only [one_smul, frame, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last]
    exact hL.1
  | cast i =>
    obtain ⟨c, -, hc1, hc⟩ := hF.1.1 P
    have hci : c i = 1 := hc1 hP i
    have hmem : (lf D F0).fl.e i ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ (lf D F0)) := by
      rw [hc]
      refine ⟨1, P.asIdeal.primeCompl.one_mem, ?_⟩
      rw [one_smul]
      have : (lf D F0).fl.e i = c i • (lf D F0).fl.e i := by rw [hci, one_smul]
      rw [this]
      exact Submodule.subset_span ⟨i, rfl⟩
    obtain ⟨s, hs, hx⟩ := hmem
    refine ⟨s, hs, ?_⟩
    simp only [frame, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc]
    exact (inf_le_left : XLam Λ (lf D F0) ≤ Λ) hx

theorem lift_transport (D : D7) (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (Λ₁ Λ₂ : Submodule (𝓞 D.host.E) (VS D).V) (h : Formalism.HermitianLatticesTheory.gmap γ Λ₁ = Λ₂) {T : D.host.E}
    (F : LFlag (D.sp.Y 0) D.R.rS T) (hL : IsLift Λ₁ F) : IsLift Λ₂ (mapLF γ F) := by
  unfold mapLF
  rw [dite_eq_left hγ]
  refine ⟨?_, ?_⟩
  · rw [← h]
    exact ⟨F.fl.z, hL.1, rfl⟩
  · show γ F.zt = γ F.fl.z
    rw [hL.2]

theorem exists_admissible_integralFrame_of_localTerms_alt : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ n m, n ∈ NRat (lf D (X.Fu u)) → m ∈ NRat (lf D (X.Fu u')) → Formalism.HermitianLatticesTheory.gmap (n⁻¹ * t₀.lin * m) t₀.lam' = t₀.lam → (∃ d, G.IsTerm d (c.lat (ρ * n) t₀.lam)) → Formalism.L2.SG.TermDef.PD D t₀.lam (lf D (X.Fu u)) u' (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))) := by
  intro D X Y u u' hst hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv n m hn hm hlam hterm
  have hγ : n⁻¹ * t₀.lin * m ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hn.1) t₀.rep.2.2.1) hm.1
  have hrow' : IsRowLat D (X.Fu u') t₀.lam' := (Y.rowsOK u').1 _ t₀.mem'
  have hrow : IsRowLat D (X.Fu u) t₀.lam := (Y.rowsOK u).1 _ t₀.mem
  have hpd' := Formalism.L2.SG.TermDef.pd_self (X.Fu u') t₀.lam' hrow'
  have hpd := Formalism.L2.SG.TermDef.pd_self (X.Fu u) t₀.lam hrow
  refine ⟨lift_transport D _ hγ _ _ hlam _ hpd'.1, ?_, GlobalTheory.T.integralRowFrame_map_isometry D _ hγ _ _ hlam _ _ hpd'.2.2⟩
  have hloc := GlobalTheory.T.movedReferenceFrame_congruent_unitriangular D X Y u u' hst hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv n m hn hm hlam hterm
  obtain ⟨ξ, h1, h2, h3⟩ := GlobalTheory.T.glue_frame_congruences_unitriangular_integral (VS D) D.R.rS t₀.lam (gS D) (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos)
    (frame (lf D (X.Fu u))) (frame (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))))
    (fun P hP a => frame_mem_locP D (X.Fu u) t₀.lam hpd.1 hpd.2.2 P hP a) hloc
  exact ⟨ξ, h1, h2, h3⟩

end GlobalTheory.HL.AdmFrame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdmissibleIntegralFrameOfLocalTermsStatement
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_admissible_integralFrame_of_localTerms : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ n m, n ∈ NRat (lf D (X.Fu u)) → m ∈ NRat (lf D (X.Fu u')) → Formalism.HermitianLatticesTheory.gmap (n⁻¹ * t₀.lin * m) t₀.lam' = t₀.lam → (∃ d, G.IsTerm d (c.lat (ρ * n) t₀.lam)) → Formalism.L2.SG.TermDef.PD D t₀.lam (lf D (X.Fu u)) u' (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))) := by
  first | exact @GlobalTheory.HL.AdmFrame.exists_admissible_integralFrame_of_localTerms_alt | exact GlobalTheory.HL.AdmFrame.exists_admissible_integralFrame_of_localTerms_alt | (intros; apply GlobalTheory.HL.AdmFrame.exists_admissible_integralFrame_of_localTerms_alt <;> assumption)
end
