module

public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
public import GroundTheory.IdeleRoots.TorusPowers.SatakeBoundAdic

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.BlockMirrorMap
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace BlockMirrorMap

theorem blk_mono {R : Type} [CommRing R] {a i j : ℕ} (hij : i ≤ j) {c : GL (Fin a) R} (h : GlobalTheory i c) : GlobalTheory j c :=
  fun p q hpq => h p q (by omega)

theorem blk_mul {R : Type} [CommRing R] {a j : ℕ} {c c' : GL (Fin a) R} (hc : GlobalTheory j c) (hc' : GlobalTheory j c') :
    GlobalTheory j (c * c') := by
  intro p q hpq
  rw [Units.val_mul]
  rcases hpq with h | h
  · calc (c.val * c'.val) p q = ((1 : Matrix (Fin a) (Fin a) R) * c'.val) p q := by
          simp only [Matrix.mul_apply]
          exact Finset.sum_congr rfl fun s _ => by rw [hc p s (Or.inl h)]
      _ = _ := by rw [Matrix.one_mul]; exact hc' p q (Or.inl h)
  · calc (c.val * c'.val) p q = (c.val * (1 : Matrix (Fin a) (Fin a) R)) p q := by
          simp only [Matrix.mul_apply]
          exact Finset.sum_congr rfl fun s _ => by rw [hc' s q (Or.inr h)]
      _ = _ := by rw [Matrix.mul_one]; exact hc p q (Or.inr h)

theorem mir_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {a m : ℕ} {g : GL (Fin a) R}
    (h : Mir m g) : Mir m (GeneralLinearGroup.map f g) := by
  intro p q hpq
  show f (g.val p q) = _
  rw [h p q hpq, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem grow {G X : Type} [TopologicalSpace G] [MulOneClass G] [ContinuousMul G] {Q : X → Prop}
    {bl bi : G → Prop} {B B' : Set G → X → Prop}
    (hbl : ∀ a b, bl a → bl b → bl (a * b)) (hi : ∀ c, bi c → bl c)
    (h : ∀ U ∈ 𝓝 (1 : G), ∃ x C, C ⊆ U ∧ Q x ∧ (∀ c ∈ C, bl c) ∧ B C x)
    (hs : ∀ U ∈ 𝓝 (1 : G), ∀ x C, Q x → B C x →
      ∃ x' C₀, C₀ ⊆ U ∧ Q x' ∧ (∀ c ∈ C₀, bi c) ∧ B' (Set.image2 (· * ·) C C₀) x') :
    ∀ U ∈ 𝓝 (1 : G), ∃ x C, C ⊆ U ∧ Q x ∧ (∀ c ∈ C, bl c) ∧ B' C x := by
  intro U hU
  obtain ⟨V, hV, hVU⟩ := exists_nhds_one_split hU
  obtain ⟨x, C, hCV, hQ, hbC, hB⟩ := h V hV
  obtain ⟨x', C₀, hC₀V, hQ', hb₀, hB'⟩ := hs V hV x C hQ hB
  refine ⟨x', Set.image2 (· * ·) C C₀, ?_, hQ', ?_, hB'⟩
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    exact hVU a (hCV ha) b (hC₀V hb)
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    exact hbl a b (hbC a ha) (hi b (hb₀ b hb))

end BlockMirrorMap

theorem kept_block_at_of_pair_level_chain_threshold : jumpWindows.MirabolicColumnBlock → jumpWindows.G0 → InfinitePlaceStep → FinitePlaceStep → K4 := by
  classical
  intro hS10 hG0 h4a h4b E _ _ _ k wt ρ J hW ψ hψ S Y hY j hj U hU x hxY hxS hxL h1
  have ins1 : InS S (1 : GA E k) := fun v _ => map_one _
  have uu1 : UU 0 (1 : GA E k) :=
    ⟨fun p q h => by rw [Units.val_one, Matrix.one_apply_ne (ne_of_lt h).symm], fun p => by simp,
      fun p q _ => rfl⟩
  have ps1 : psN ψ (1 : GA E k) = 1 := by
    have e : (∑ p : Fin k × Fin k with (p.2 : ℕ) = p.1 + 1, (1 : GA E k).val p.1 p.2) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      rw [Finset.mem_filter] at hp
      rw [Units.val_one, Matrix.one_apply_ne]
      intro h
      rw [h] at hp
      omega
    unfold psN
    rw [e, AddChar.map_zero_eq_one]
  have om0 : ∀ g : GA E k, Om 0 0 g → g = 1 := by
    intro g hg
    apply (hG0 E k).2.2.2.2.2.1
    · rw [(hS10 _ k 0).2.1 _ hg.1, map_one]
    · intro v
      rw [(hS10 _ k 0).2.1 _ (hg.2 v), map_one]
  have start : Bump ψ S (Om 0 0) {1} (Wh ψ (J x)) := by
    refine ⟨isCompact_singleton, ?_, ⟨1, one_pos, by rw [h1]; simp⟩, ?_⟩
    · intro c hc
      rw [Set.mem_singleton_iff.mp hc]
      exact ins1
    · intro g hg _
      obtain rfl := om0 g hg
      exact ⟨1, 1, rfl, 1, uu1, ins1, (mul_one 1).symm, zero_le_one, by rw [h1, ps1]; simp⟩
  let P : ℕ → (Pl E → ℕ) → Prop := fun n m => ∀ V ∈ 𝓝 (1 : GA E k), ∃ x' C, C ⊆ V ∧
    (J x' ∈ Y ∧ SmV (ρ.comp (infGL E k)) x' ∧ Lev S (J x')) ∧ (∀ c ∈ C, GlobalTheory j c) ∧
      Bump ψ S (Om n m) C (Wh ψ (J x'))
  have p0 : P 0 0 := by
    intro V hV
    exact ⟨x, {1}, Set.singleton_subset_iff.mpr (mem_of_mem_nhds hV), ⟨hxY, hxS, hxL⟩,
      fun c hc => by rw [Set.mem_singleton_iff.mp hc]; exact (hS10 _ k j).2.2.2.1, start⟩
  have stepInf : ∀ n, n ≤ j → P n 0 := by
    intro n
    induction n with
    | zero => intro _; exact p0
    | succ n ih =>
      intro hn
      refine BlockMirrorMap.grow (fun a b ha hb => BlockMirrorMap.blk_mul ha hb) (fun c hc => BlockMirrorMap.blk_mono hn hc) (ih (by omega)) ?_
      intro V hV x C hQ hB
      obtain ⟨x', C₀, a, b, c, d, e, f⟩ :=
        h4a E k wt ρ J hW ψ hψ S Y hY n 0 (by omega) (fun _ _ => rfl) V hV x C hQ.1 hQ.2.1 hQ.2.2 hB
      exact ⟨x', C₀, a, ⟨b, c, d⟩, e, f⟩
  have stepFin : ∀ (v : Pl E), v ∈ S → ∀ m : Pl E → ℕ, m v = 0 → (∀ u, u ∉ S → m u = 0) → P j m →
      ∀ i, i ≤ j → P j (Function.update m v i) := by
    intro v hv m hmv hm hP i
    induction i with
    | zero => intro _; rw [Function.update_eq_self_iff.mpr hmv.symm]; exact hP
    | succ i ih =>
      intro hi
      have supp : ∀ u, u ∉ S → Function.update m v i u = 0 := by
        intro u hu
        have hne : u ≠ v := fun h => hu (h ▸ hv)
        rw [Function.update_of_ne hne]
        exact hm u hu
      refine BlockMirrorMap.grow (bi := fun c => GlobalTheory (Function.update m v i v + 1) c) (fun a b ha hb => BlockMirrorMap.blk_mul ha hb)
        (fun c hc => BlockMirrorMap.blk_mono (by simp; omega) hc) (ih (by omega)) ?_
      intro V hV x C hQ hB
      obtain ⟨x', C₀, a, b, c, d, e, f⟩ :=
        h4b E k wt ρ J hW ψ hψ S Y hY j (Function.update m v i) v hv (by simp; omega) supp V hV x C
          hQ.1 hQ.2.1 hQ.2.2 hB
      simp only [Function.update_self, Function.update_idem] at f
      exact ⟨x', C₀, a, ⟨b, c, d⟩, e, f⟩
  have key : ∀ T : Finset (Pl E), T ⊆ S → P j (fun w => if w ∈ T then j else 0) := by
    intro T
    refine Finset.induction_on T ?_ ?_
    · intro _
      have e : (fun w : Pl E => if w ∈ (∅ : Finset (Pl E)) then j else 0) = 0 := by
        funext w
        simp
      rw [e]
      exact stepInf j le_rfl
    · intro v T hv ih hT
      have h := stepFin v (hT (Finset.mem_insert_self v T)) (fun w => if w ∈ T then j else 0)
        (by simp [hv]) (fun u hu => by simp [show u ∉ T from fun h => hu (hT (Finset.mem_insert_of_mem h))])
        (ih (subset_trans (Finset.subset_insert v T) hT)) j le_rfl
      convert h using 1
      funext w
      by_cases hw : w = v
      · subst hw; simp
      · simp [hw]
  obtain ⟨x', C, hCU, ⟨hY', hS', hL'⟩, hbl, hB⟩ := key S subset_rfl U hU
  refine ⟨x', C, hCU, hY', hS', hL', hbl, hB.1, hB.2.1, hB.2.2.1, fun g hg hW0 => hB.2.2.2 g ?_ hW0⟩
  refine ⟨BlockMirrorMap.mir_map _ hg.2, fun v => ?_⟩
  by_cases hv : v ∈ S
  · simp only [hv, if_true]
    exact BlockMirrorMap.mir_map _ hg.2
  · simp only [hv, if_false]
    rw [hg.1 v hv]
    exact (hS10 _ k 0).2.2.1

end PositivityTheory.AdelicQuotientData

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.LastRowIntegral
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace LastRowIntegral

open ValuativeRel

theorem mul_apply_last {R : Type*} [CommRing R] {n : ℕ} (A B : Matrix (Fin n) (Fin n) R) (i : Fin n)
    (hi : (i : ℕ) + 1 = n) (h0 : ∀ j, j < i → A i j = 0) (h1 : A i i = 1) (c : Fin n) : (A * B) i c = B i c := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [h1, one_mul]
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h | h
    · rw [h0 j h, zero_mul]
    · exfalso
      have h2 := j.isLt
      have h3 : (i : ℕ) < j := h
      omega
  · intro h; exact absurd (Finset.mem_univ i) h

variable {E : Type} [Field E] [NumberField E]

theorem lastRow_eq {k : ℕ} (hk : 1 ≤ k) (g : GA E k) (c : Fin k) :
    lastRow g c = g.val ⟨k - 1, by omega⟩ c := by
  unfold lastRow
  rw [Finset.sum_eq_single ⟨k - 1, by omega⟩]
  · rw [if_pos (by simp only; omega)]
  · intro j _ hj
    rw [if_neg]
    intro h; apply hj; ext; simp only; omega
  · intro h; exact absurd (Finset.mem_univ _) h

theorem lastRow_UU {k : ℕ} (hk : 1 ≤ k) {n : GA E k} (hn : UU 0 n) (g : GA E k) :
    lastRow (n * g) = lastRow g := by
  funext c
  rw [lastRow_eq hk, lastRow_eq hk, Units.val_mul]
  refine mul_apply_last _ _ _ (by simp only; omega) (fun j hj => hn.1 _ _ hj) (hn.2.1 _) c

theorem continuous_lastRow {k : ℕ} : Continuous (lastRow : GA E k → Fin k → Ad E) := by
  refine continuous_pi fun c => continuous_finsetSum _ fun i _ => ?_
  split_ifs
  · exact Units.continuous_val.matrix_elem i c
  · exact continuous_const

theorem continuous_sFin : Continuous (sFin E) :=
  (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))

theorem mem_int (w : Pl E) (x : w.adicCompletion E) (hx : x ∈ 𝒪[w.adicCompletion E]) :
    x ∈ w.adicCompletionIntegers E := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  have hO : 𝒪[w.adicCompletion E] = (w.adicCompletionIntegers E).toSubring := by
    ext y
    rw [Valuation.mem_integer_iff, he.le_one_iff_le_one]
    exact Iff.rfl
  rw [hO] at hx
  exact hx

end LastRowIntegral

namespace LastRowIntegral

open ValuativeRel GroundTheory.Automorphic.Iwasawa

theorem last_int {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {k m : ℕ} (hk : 1 ≤ k) (hkm : k < m) (ιw : GL (Fin k) F →* GL (Fin m) F)
    (hu : ∀ n ∈ unipotent F k, ιw n ∈ unipotent F m)
    (hκ : ∀ κ ∈ GLnLocal.integralGL F k, ιw κ ∈ GLnLocal.integralGL F m)
    (ht : ∀ l, ιw (torusPow F k l) = torusPow F m (pad m l)) (h : GL (Fin k) F)
    (ha : Antitone (iwasawaExponent F m (ιw h))) (c : Fin k) : h ⟨k - 1, by omega⟩ c ∈ 𝒪[F] := by
  obtain ⟨u, hu0, κ, hκ0, he⟩ := exists_eq_mul_torusPow_iwasawaExponent F k h
  set l := iwasawaExponent F k h
  have hl : iwasawaExponent F m (ιw h) = pad m l := by
    rw [he, map_mul, map_mul, ht]
    exact iwasawaExponent_eq F m (hu u hu0) (hκ κ hκ0)
  rw [hl] at ha
  have h0 : 0 ≤ l ⟨k - 1, by omega⟩ := by
    have := ha (show (⟨k - 1, by omega⟩ : Fin m) ≤ ⟨k, hkm⟩ from Fin.mk_le_mk.2 (by omega))
    simpa [pad, show k - 1 < k by omega] using this
  obtain ⟨e, he'⟩ := Int.eq_ofNat_of_zero_le h0
  rw [he, Units.val_mul, Units.val_mul, Matrix.mul_assoc,
    mul_apply_last _ _ _ (by simp only; omega) (fun j hj => hu0.1 hj) (hu0.2 _) c, coe_torusPow,
    Matrix.diagonal_mul, he', zpow_natCast]
  exact Subring.mul_mem _ (Subring.pow_mem _ (GLnLocal.uniformizer F).2 _)
    (((GLnLocal.mem_integralGL_iff F k).1 hκ0).1 _ _)

end LastRowIntegral

theorem last_row_integral_of : jumpWindows.G0 → CornerEmbedding → K8 → K6 := by
  intro hG0 h5 h8 E _ _ _ m k hk hkm ψ hψ S hS ι hι α M U φ hP
  obtain ⟨hex, hι5⟩ := h5 E m k hkm.le
  obtain ⟨-, hblk, hsurj, -, -, hcpt, -, hloc, hcInf, hUU, -⟩ := hι5 ι hι
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hg0, -, -, -, -⟩ := hG0 E k
  obtain ⟨-, -, hW⟩ := h8 E m ψ hψ S hS α φ hP.good hP.sat
  obtain ⟨C, -, hCblk, hCcpt, -, -, hB⟩ := hP.bump
  choose ιw hιw using fun w : Pl E => hex (w.adicCompletion E)
  have hlw := fun w => hloc w (ιw w) (hιw w)
  refine ⟨(fun p => p.1 + p.2) '' ((lastRow '' (ι ⁻¹' C)) ×ˢ
    Set.pi Set.univ (fun _ => sFin E '' (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E : Set (Af E)))), ?_, ?_⟩
  · exact (((hcpt C hCcpt).image LastRowIntegral.continuous_lastRow).prod (isCompact_univ_pi fun _ =>
      (GroundTheory.Global.isCompact_integralFiniteAdeles E).image LastRowIntegral.continuous_sFin)).image
      (continuous_fst.add continuous_snd)
  intro g hg
  obtain ⟨hW1, hW2⟩ := hW (ι g) hg
  obtain ⟨g₀, h0i, h0S, h0in⟩ := hg0 S g
  have hinf : cInf (ι g₀) = cInf (ι g) := by
    have e : g = g₀ * (g₀⁻¹ * g) := by group
    have h1 : cInf (g₀⁻¹ * g) = 1 := by rw [map_mul, map_inv, h0i, inv_mul_cancel]
    conv_rhs => rw [e, map_mul, map_mul, hcInf _ h1, mul_one]
  have hSl : ∀ w ∈ S, cLoc w (ι g₀) = cLoc w (ι g) := fun w hw => by
    rw [(hlw w).2.1, (hlw w).2.1, h0S w hw]
  have hin : InS S (ι g₀) := fun w hw => by rw [(hlw w).2.1, h0in w hw, map_one]
  have hne := hW1 (ι g₀) hinf hSl hin
  have hmir : Mir k (ι g₀) := fun i c h => hblk g₀ i c (h.imp id Nat.le_of_lt)
  obtain ⟨n, c, hc, t, hn, -, heq, -, -⟩ := hB (ι g₀) ⟨hin, hmir⟩ hne
  obtain ⟨c', rfl⟩ := hsurj c (hCblk c hc)
  have hn' : n = ι (g₀ * c'⁻¹) := by rw [map_mul, map_inv, heq, mul_inv_cancel_right]
  have hU0 : UU 0 (g₀ * c'⁻¹) := (hUU _).1 (hn' ▸ hn)
  have hA : lastRow g₀ = lastRow c' := by
    conv_lhs => rw [show g₀ = (g₀ * c'⁻¹) * c' by group]
    exact LastRowIntegral.lastRow_UU hk hU0 c'
  refine ⟨(lastRow g₀, lastRow g - lastRow g₀), ⟨⟨c', hc, hA.symm⟩, fun i _ => ?_⟩, by simp⟩
  refine ⟨pFin E ((lastRow g - lastRow g₀) i), ?_, ?_⟩
  · intro v
    change pLoc E v (pFin E ((lastRow g - lastRow g₀) i)) ∈ v.adicCompletionIntegers E
    rw [Pi.sub_apply, LastRowIntegral.lastRow_eq hk, LastRowIntegral.lastRow_eq hk, map_sub, map_sub]
    change (cLoc v g).val _ i - (cLoc v g₀).val _ i ∈ v.adicCompletionIntegers E
    by_cases hv : v ∈ S
    · rw [h0S v hv, sub_self]; exact zero_mem _
    · rw [h0in v hv]
      refine sub_mem (LastRowIntegral.mem_int v _ ?_) (LastRowIntegral.mem_int v _ ?_)
      · have ha := hW2 v hv
        rw [(hlw v).2.1] at ha
        exact LastRowIntegral.last_int hk hkm (ιw v) (hlw v).2.2.1 (hlw v).2.2.2.1 (hlw v).2.2.2.2 _ ha i
      · change (1 : Matrix (Fin k) (Fin k) (v.adicCompletion E)) _ i ∈ _
        rw [Matrix.one_apply]
        split_ifs
        · exact one_mem _
        · exact zero_mem _
  · refine ad_ext ?_ rfl
    change (infEq E).symm 0 = _
    rw [map_zero]
    change (0 : Cinf E) = pInf E ((lastRow g - lastRow g₀) i)
    rw [Pi.sub_apply, LastRowIntegral.lastRow_eq hk, LastRowIntegral.lastRow_eq hk, map_sub]
    change (0 : Cinf E) = (cInf g).val _ i - (cInf g₀).val _ i
    rw [h0i, sub_self]

end PositivityTheory.AdelicQuotientData

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.BaseRankDimension
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace BaseRankDimension

open scoped ValuativeRel

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem dt_pos (g : GA E k) : 0 < Dt g := (GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det g)).2

theorem dt_mul (g h : GA E k) : Dt (g * h) = Dt g * Dt h := by
  simp only [Dt, map_mul, Positive.val_mul]

theorem continuous_det' : Continuous (GeneralLinearGroup.det : GA E k → (Ad E)ˣ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Units.continuous_val.matrix_det
  · have : (fun g : GA E k => (((GeneralLinearGroup.det g)⁻¹ : (Ad E)ˣ) : Ad E)) =
        fun g : GA E k => ((g⁻¹ : GA E k) : Matrix (Fin k) (Fin k) (Ad E)).det := by
      funext g; rw [← map_inv]; rfl
    rw [this]
    exact (Units.continuous_val.comp continuous_inv).matrix_det

theorem dt_cont : Continuous (Dt : GA E k → ℝ) :=
  continuous_subtype_val.comp (GroundTheory.Global.IdeleGroup.continuous_ideleModule.comp continuous_det')

theorem dt_rat (γ : GL (Fin k) E) : Dt (ratGL E k γ) = 1 := by
  have h : GeneralLinearGroup.det (ratGL E k γ) = GroundTheory.Global.IdeleGroup.diagonal E (GeneralLinearGroup.det γ) :=
    Units.ext (by rw [ratGL, GlobalTheory.CuspRep.det_map]; rfl)
  rw [Dt, h, GroundTheory.Global.IdeleGroup.ideleModule_diagonal, Positive.val_one]

theorem dt_uu (j : ℕ) (u : GA E k) (hu : UU j u) : Dt u = 1 := by
  have h : GeneralLinearGroup.det u = 1 := by
    refine Units.ext ?_
    change (u : Matrix (Fin k) (Fin k) (Ad E)).det = 1
    rw [Matrix.det_of_isUpperTriangular (fun i c hc => hu.1 i c hc)]
    exact Finset.prod_eq_one fun i _ => hu.2.1 i
  rw [Dt, h, map_one, Positive.val_one]

theorem dt_invT (g : GA E k) : Dt (invT g) = (Dt g)⁻¹ := by
  have h : GeneralLinearGroup.det (invT g) = (GeneralLinearGroup.det g)⁻¹ := by
    rw [← map_inv]
    refine Units.ext ?_
    change ((g⁻¹ : GA E k) : Matrix (Fin k) (Fin k) (Ad E))ᵀ.det = _
    rw [Matrix.det_transpose]; rfl
  rw [Dt, Dt, h, map_inv]
  rfl

variable [_root_.NumberField.IsTotallyComplex E]

theorem dt_eq (g : GA E k) : Dt g =
    (∏ w : InfinitePlace E, ‖((GeneralLinearGroup.det (jumpWindows.cInf g) : (Cinf E)ˣ) : Cinf E) w‖ ^ w.mult) *
      ∏ᶠ v : Pl E, ‖((GeneralLinearGroup.det (jumpWindows.cLoc v g) : (v.adicCompletion E)ˣ) : v.adicCompletion E)‖ := by
  rw [Dt, GroundTheory.Global.IdeleGroup.ideleModule_eq]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [jumpWindows.cInf, GlobalTheory.CuspRep.det_map]
    congr 1
    exact ((InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _).symm
  · refine finprod_congr fun v => ?_
    rw [jumpWindows.cLoc, GlobalTheory.CuspRep.det_map]
    rfl

theorem inf_one : (∏ w : InfinitePlace E, ‖((GeneralLinearGroup.det (1 : GL (Fin k) (Cinf E)) : (Cinf E)ˣ) : Cinf E) w‖ ^ w.mult) = 1 := by
  simp

omit [_root_.NumberField.IsTotallyComplex E] in
theorem nrm_pi (l : ℤ) (w : Pl E) :
    ‖(GLnLocal.uniformizer (w.adicCompletion E) : w.adicCompletion E) ^ l‖ = (Ideal.absNorm w.asIdeal : ℝ) ^ (-l) := by
  have h0 : (GLnLocal.uniformizer (w.adicCompletion E) : w.adicCompletion E) ≠ 0 := fun h =>
    (GLnLocal.irreducible_uniformizer (w.adicCompletion E)).ne_zero (Subtype.ext h)
  rw [norm_zpow, ← GroundTheory.Global.normalizedAbv_apply, GroundTheory.Global.normalizedAbv_eq_zpow w h0,
    GroundTheory.BlockD.SatakeBound.valued_uniformizer_eq w, WithZero.log_exp, ← _root_.zpow_mul, neg_one_mul]

theorem dt_fl (h3 : ∀ (w : Pl E) (u : GL (Fin k) (w.adicCompletion E)), jumpWindows.cInf (fl k w u : GA E k) = 1)
    (h4 : ∀ (w : Pl E) (u : GL (Fin k) (w.adicCompletion E)), jumpWindows.cLoc w (fl k w u : GA E k) = u)
    (h5 : ∀ (w v : Pl E) (u : GL (Fin k) (w.adicCompletion E)), v ≠ w → jumpWindows.cLoc v (fl k w u : GA E k) = 1)
    (w : Pl E) (x : GL (Fin k) (w.adicCompletion E)) :
    Dt (fl k w x) = ‖((GeneralLinearGroup.det x : (w.adicCompletion E)ˣ) : w.adicCompletion E)‖ := by
  rw [dt_eq, h3, inf_one, one_mul, finprod_eq_single _ w (fun v hv => by rw [h5 w v x hv, map_one, Units.val_one, norm_one]), h4]

theorem dt_torus (h3 : ∀ (w : Pl E) (u : GL (Fin k) (w.adicCompletion E)), jumpWindows.cInf (fl k w u : GA E k) = 1)
    (h4 : ∀ (w : Pl E) (u : GL (Fin k) (w.adicCompletion E)), jumpWindows.cLoc w (fl k w u : GA E k) = u)
    (h5 : ∀ (w v : Pl E) (u : GL (Fin k) (w.adicCompletion E)), v ≠ w → jumpWindows.cLoc v (fl k w u : GA E k) = 1)
    (w : Pl E) (l : Fin k → ℤ) :
    Dt (fl k w (Iwasawa.torusPow (w.adicCompletion E) k l)) = (Ideal.absNorm w.asIdeal : ℝ) ^ (-∑ i, l i) := by
  rw [dt_fl h3 h4 h5]
  change ‖((Iwasawa.torusPow (w.adicCompletion E) k l : GL (Fin k) (w.adicCompletion E)) :
    Matrix (Fin k) (Fin k) (w.adicCompletion E)).det‖ = _
  rw [Iwasawa.coe_torusPow, Matrix.det_diagonal, norm_prod]
  simp only [nrm_pi]
  have hN : (Ideal.absNorm w.asIdeal : ℝ) ≠ 0 := by
    exact_mod_cast NumberField.HeightOneSpectrum.absNorm_ne_zero w
  rw [← Finset.sum_neg_distrib]
  refine Finset.induction_on (Finset.univ : Finset (Fin k)) (by simp) ?_
  intro a s ha ih
  rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hN]

theorem dt_split (h1 : ∀ y, jumpWindows.cInf (infGL E k y) = y) (h2 : ∀ (w : Pl E) y, jumpWindows.cLoc w (infGL E k y) = 1) (t : ℝ) :
    Dt (splitCentre E k t) = Real.exp (k * Module.finrank ℚ E * t) := by
  rw [dt_eq, splitCentre, h1]
  simp only [h2, map_one, Units.val_one, norm_one, finprod_one, mul_one]
  have e : ∀ w : InfinitePlace E, ‖((GeneralLinearGroup.det (Units.map (Matrix.scalar (Fin k)).toMonoidHom
      (expU fun _ : InfinitePlace E => (t : ℂ))) : (Cinf E)ˣ) : Cinf E) w‖ = Real.exp t ^ k := by
    intro w
    change ‖(Matrix.scalar (Fin k) ((expU fun _ : InfinitePlace E => (t : ℂ) : (Cinf E)ˣ) : Cinf E)).det w‖ = _
    simp [expU, Complex.norm_exp]
  simp only [e]
  rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq, ← pow_mul, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem dt_kappa (κ : GA E k) (hκ : jumpWindows.cInf κ = 1)
    (hint : ∀ w : Pl E, jumpWindows.cLoc w κ ∈ GLnLocal.integralGL (w.adicCompletion E) k) : Dt κ = 1 := by
  rw [dt_eq, hκ, inf_one, one_mul]
  refine finprod_eq_one_of_forall_eq_one fun v => ?_
  obtain ⟨u, hu⟩ := hint v
  rw [← hu]
  set d := GeneralLinearGroup.det u with hd
  have ex : ((GeneralLinearGroup.det (GLnLocal.integralGLHom (v.adicCompletion E) k u) : (v.adicCompletion E)ˣ) :
      v.adicCompletion E) = ((d : 𝒪[v.adicCompletion E]) : v.adicCompletion E) := by
    change (Matrix.det ((RingHom.mapMatrix (𝒪[v.adicCompletion E]).subtype) (u : Matrix (Fin k) (Fin k) _))) = _
    rw [← RingHom.map_det]
    rfl
  rw [ex]
  set x : v.adicCompletion E := ((d : 𝒪[v.adicCompletion E]) : v.adicCompletion E) with hx
  have hx0 : x ≠ 0 := fun h => d.ne_zero (Subtype.ext h)
  have hv1 : Valued.v x ≤ 1 := GroundTheory.BlockD.SatakeBound.valued_le_one_of_mem (w := v) (d : 𝒪[v.adicCompletion E]).2
  have hxy : x * ((d⁻¹ : (𝒪[v.adicCompletion E])ˣ) : v.adicCompletion E) = 1 := by
    rw [hx, ← Subring.coe_mul, Units.mul_inv]; rfl
  have hv2 : Valued.v ((d⁻¹ : (𝒪[v.adicCompletion E])ˣ) : v.adicCompletion E) ≤ 1 :=
    GroundTheory.BlockD.SatakeBound.valued_le_one_of_mem (w := v) ((d⁻¹ : (𝒪[v.adicCompletion E])ˣ) : 𝒪[v.adicCompletion E]).2
  have hv : Valued.v x = 1 := by
    refine le_antisymm hv1 ?_
    calc (1 : WithZero (Multiplicative ℤ)) = Valued.v x * Valued.v ((d⁻¹ : (𝒪[v.adicCompletion E])ˣ) : v.adicCompletion E) := by
          rw [← map_mul, hxy, map_one]
      _ ≤ Valued.v x * 1 := by gcongr
      _ = Valued.v x := mul_one _
  rw [← GroundTheory.Global.normalizedAbv_apply, GroundTheory.Global.normalizedAbv_eq_zpow v hx0, hv, WithZero.log_one, zpow_zero]

end BaseRankDimension

theorem determinant_basic_of_G0 : jumpWindows.G0 → D0 := by
  intro hG E _ _ _ k
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := hG E k
  exact ⟨BaseRankDimension.dt_pos, BaseRankDimension.dt_mul, BaseRankDimension.dt_cont, BaseRankDimension.dt_rat, BaseRankDimension.dt_uu, BaseRankDimension.dt_invT, BaseRankDimension.dt_split h1 h2,
    fun t g => GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm t g, fun s t => GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_add s t,
    BaseRankDimension.dt_torus h3 h4 h5, fun κ hκ hint => BaseRankDimension.dt_kappa κ hκ hint⟩

end PositivityTheory.AdelicQuotientData

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnBlockEquiv
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace ColumnBlockEquiv

section Ring

variable {R : Type} [CommRing R] {a : ℕ}

theorem pm_col (m : ℕ) (y : UnipotentBlockColumnIndex a m m → R) (i k : Fin a) :
    posM (Subtype.val : UnipotentBlockColumnIndex a m m → Fin a × Fin a) y i k =
      if hik : (i : ℕ) < m ∧ (k : ℕ) = m then y ⟨(i, k), hik.1, hik.2.ge, hik.2.le⟩ else 0 := by
  rw [posM, Matrix.sum_apply]
  split_ifs with hik
  · rw [Finset.sum_eq_single ⟨(i, k), hik.1, hik.2.ge, hik.2.le⟩]
    · simp
    · intro b _ hb
      rw [Matrix.single_apply, if_neg]
      rintro ⟨h1, h2⟩
      exact hb (Subtype.ext (Prod.ext h1 h2))
    · intro h
      exact absurd (Finset.mem_univ _) h
  · refine Finset.sum_eq_zero fun t _ => ?_
    rw [Matrix.single_apply, if_neg]
    rintro ⟨h1, h2⟩
    apply hik
    have := t.2
    rw [← h1, ← h2]
    omega

theorem pm_mul_apply {ι : Type} [Fintype ι] (p : ι → Fin a × Fin a) (y : ι → R)
    (M : Matrix (Fin a) (Fin a) R) (i k : Fin a) :
    (posM p y * M) i k = ∑ s, if (p s).1 = i then y s * M (p s).2 k else 0 := by
  simp only [posM, Matrix.sum_mul, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : (p s).1 = i
  · subst h
    simp [Matrix.single_mul_apply_same]
  · rw [if_neg h, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Matrix.single_apply, if_neg (fun e => h e.1), zero_mul]

theorem mul_pm_apply {ι : Type} [Fintype ι] (p : ι → Fin a × Fin a) (y : ι → R)
    (M : Matrix (Fin a) (Fin a) R) (i k : Fin a) :
    (M * posM p y) i k = ∑ s, if (p s).2 = k then M i (p s).1 * y s else 0 := by
  simp only [posM, Matrix.mul_sum, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : (p s).2 = k
  · subst h
    simp [Matrix.mul_single_apply_same]
  · rw [if_neg h, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Matrix.single_apply, if_neg (fun e => h e.2), mul_zero]

theorem pm_mul_row (m : ℕ) (y : UnipotentBlockColumnIndex a m m → R) (M : Matrix (Fin a) (Fin a) R)
    (hM : ∀ j k : Fin a, (j : ℕ) = m → M j k = (1 : Matrix (Fin a) (Fin a) R) j k) :
    posM (Subtype.val : UnipotentBlockColumnIndex a m m → Fin a × Fin a) y * M = posM Subtype.val y := by
  ext i k
  have e := pm_mul_apply (Subtype.val : UnipotentBlockColumnIndex a m m → Fin a × Fin a) y 1 i k
  rw [Matrix.mul_one] at e
  rw [e, pm_mul_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hM s.1.2 k (by have := s.2; omega)]

theorem mul_posM_blockColumn (m : ℕ) (y : UnipotentBlockColumnIndex a m m → R) (h : GL (Fin a) R) (hB : GlobalTheory m h) :
    h.val * posM (Subtype.val : UnipotentBlockColumnIndex a m m → Fin a × Fin a) y =
      posM Subtype.val (fun t : UnipotentBlockColumnIndex a m m => ∑ s, h.val t.1.1 s.1.1 * y s) := by
  ext i k
  rw [mul_pm_apply, pm_col]
  split_ifs with hc
  · refine Finset.sum_congr rfl fun s _ => ?_
    rw [if_pos (Fin.ext (by have := s.2; omega))]
  · refine Finset.sum_eq_zero fun s _ => ?_
    split_ifs with hs
    · have h2 := s.2
      have hk : (k : ℕ) = m := by rw [← hs]; omega
      have hi : m ≤ (i : ℕ) := by
        by_contra hh
        exact hc ⟨by omega, hk⟩
      rw [hB i s.1.1 (Or.inl hi), Matrix.one_apply_ne, zero_mul]
      intro e
      rw [← e] at h2
      omega
    · rfl

theorem conj_blkU (m : ℕ) (h : GL (Fin a) R) (hB : GlobalTheory m h) (y : UnipotentBlockColumnIndex a m m → R) :
    h * blkU y * h⁻¹ = blkU (fun t : UnipotentBlockColumnIndex a m m => ∑ s, h.val t.1.1 s.1.1 * y s) := by
  have e : h * blkU y = blkU (fun t : UnipotentBlockColumnIndex a m m => ∑ s, h.val t.1.1 s.1.1 * y s) * h := by
    apply Units.ext
    show h.val * (1 + posM Subtype.val y) = (1 + posM Subtype.val _) * h.val
    rw [mul_add, add_mul, mul_one, one_mul,
      pm_mul_row m _ h.val (fun j k hj => hB j k (Or.inl hj.ge)), mul_posM_blockColumn m y h hB]
  rw [e, mul_inv_cancel_right]

end Ring

def colEquiv (k j : ℕ) (hj : j < k) : UnipotentBlockColumnIndex k j j ≃ Fin j where
  toFun t := ⟨t.1.1.val, t.2.1⟩
  invFun i := ⟨(⟨i.val, i.2.trans hj⟩, ⟨j, hj⟩), i.2, le_rfl, le_rfl⟩
  left_inv t := Subtype.ext (Prod.ext rfl (Fin.ext (by
    have := t.2.2
    change j = (t.1.2 : ℕ)
    omega)))
  right_inv i := Fin.ext rfl

end ColumnBlockEquiv

theorem algebraic_modulus_one_of_finiteOrder_char : AdelicLinearChange → CornerEmbedding → ColumnConjugationMeasure := by
  intro hM hK E _ _ _ k j hj g hg F hF
  have hK' := hK E k j hj.le
  obtain ⟨ι, hι⟩ := hK'.1 (Ad E)
  have hK2 := hK'.2 ι hι
  obtain ⟨g', rfl⟩ := hK2.2.2.1 g hg
  have hDt : Dt (ι g') = Dt g' := hK2.2.2.2.1 g'
  let e : UnipotentBlockColumnIndex k j j ≃ Fin j := ColumnBlockEquiv.colEquiv k j hj
  let Φ := MeasurableEquiv.piCongrLeft (fun _ : Fin j => Ad E) e
  have hΦ : MeasurePreserving Φ (vecMeasure E (UnipotentBlockColumnIndex k j j)) (vecMeasure E (Fin j)) :=
    measurePreserving_piCongrLeft (fun _ : Fin j => GroundTheory.Global.adeleMeasure E) e
  have key : ∀ H : (UnipotentBlockColumnIndex k j j → Ad E) → ℝ≥0∞,
      ∫⁻ y, H y ∂vecMeasure E (UnipotentBlockColumnIndex k j j) = ∫⁻ v, H (Φ.symm v) ∂vecMeasure E (Fin j) := by
    intro H
    have h1 := hΦ.lintegral_comp_emb Φ.measurableEmbedding (fun v => H (Φ.symm v))
    simp only [MeasurableEquiv.symm_apply_apply] at h1
    exact h1
  have hsymm : ∀ (v : Fin j → Ad E) (t : UnipotentBlockColumnIndex k j j), Φ.symm v t = v (e t) := by
    intro v t
    rfl
  have hent : ∀ t s : UnipotentBlockColumnIndex k j j, (ι g').val t.1.1 s.1.1 = g'.val (e t) (e s) := by
    intro t s
    rw [hι g']
    exact dif_pos ⟨t.2.1, s.2.1⟩
  have hpt : ∀ v : Fin j → Ad E, ι g' * blkU (Φ.symm v) * (ι g')⁻¹ =
      blkU (fun t : UnipotentBlockColumnIndex k j j => (g'.val *ᵥ v) (e t)) := by
    intro v
    rw [PositivityTheory.AdelicQuotientData.ColumnBlockEquiv.conj_blkU j (ι g') hg]
    refine congrArg blkU (funext fun t => ?_)
    rw [show (g'.val *ᵥ v) (e t) = ∑ b, g'.val (e t) b * v b from rfl, ← e.sum_comp]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hsymm, hent t s]
  have hc : Continuous (fun v : Fin j → Ad E => (blkU (fun t : UnipotentBlockColumnIndex k j j => v (e t)) : GA E k)) :=
    (continuous_posU (isNil_blk k j j)).comp (continuous_pi fun t => continuous_apply (e t))
  have hG : Measurable (fun v : Fin j → Ad E => F (blkU (fun t : UnipotentBlockColumnIndex k j j => v (e t)))) :=
    hF.comp hc.measurable
  calc ∫⁻ x, F (ι g' * blkU x * (ι g')⁻¹) ∂vecMeasure E (UnipotentBlockColumnIndex k j j)
      = ∫⁻ v, F (ι g' * blkU (Φ.symm v) * (ι g')⁻¹) ∂vecMeasure E (Fin j) :=
        key (fun x => F (ι g' * blkU x * (ι g')⁻¹))
    _ = ∫⁻ v, F (blkU (fun t : UnipotentBlockColumnIndex k j j => (g'.val *ᵥ v) (e t))) ∂vecMeasure E (Fin j) :=
        lintegral_congr fun v => by rw [hpt v]
    _ = ENNReal.ofReal (Dt g')⁻¹ *
          ∫⁻ v, F (blkU (fun t : UnipotentBlockColumnIndex k j j => v (e t))) ∂vecMeasure E (Fin j) :=
        (hM E j g' _ hG).1
    _ = ENNReal.ofReal (Dt (ι g'))⁻¹ * ∫⁻ x, F (blkU x) ∂vecMeasure E (UnipotentBlockColumnIndex k j j) := by
        rw [hDt, key (fun x => F (blkU x))]
        congr 1

end PositivityTheory.AdelicQuotientData

end
end

section -- merged from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.SmoothVectorHyp
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace SmoothVectorHyp

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

structure Hyp (E : Type) [Field E] [NumberField E] (k : ℕ) : Prop where
  cont : Continuous (dmin : GA E k → ℝ)
  pos : ∀ g : GA E k, 0 < dmin g
  rt : ∀ h : GA E k, ∃ B : ℝ, 1 ≤ B ∧ ∀ g, dmin (g * h) ≤ B * dmin g

lemma min_le_of (a b D : ℝ) (hD : 1 ≤ D) (h : a ≤ D * b) : min 1 a ≤ D * min 1 b := by
  rcases le_total 1 b with h1 | h1
  · rw [min_eq_left h1]; exact (min_le_left _ _).trans (by linarith)
  · rw [min_eq_right h1]; exact (min_le_right _ _).trans h

lemma wt_pos (H : Hyp E k) (M : ℕ) (g : GA E k) : 0 < wt M g :=
  pow_pos (lt_min one_pos (H.pos g)) M

lemma wt_le_one (H : Hyp E k) (M : ℕ) (g : GA E k) : wt M g ≤ 1 :=
  pow_le_one₀ (le_min zero_le_one (H.pos g).le) (min_le_left _ _)

lemma wt_cont (H : Hyp E k) (M : ℕ) : Continuous (wt M : GA E k → ℝ) :=
  (continuous_const.min H.cont).pow M

lemma wt_le (H : Hyp E k) (M : ℕ) (g c : GA E k) (D : ℝ) (hD : 1 ≤ D)
    (h : dmin (g * c) ≤ D * dmin g) : wt M (g * c) ≤ D ^ M * wt M g := by
  unfold wt
  rw [← mul_pow]
  exact pow_le_pow_left₀ (le_min zero_le_one (H.pos _).le) (min_le_of _ _ _ hD h) M

def W (H : Hyp E k) (M : ℕ) : XB E k :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun g => ((wt M g : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp (wt_cont H M)) 1 fun g => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (wt_pos H M g).le]
      exact wt_le_one H M g

lemma ratio_cont (H : Hyp E k) (M : ℕ) (h : GA E k) :
    Continuous fun g : GA E k => ((wt M (g * h) / wt M g : ℝ) : ℂ) :=
  Complex.continuous_ofReal.comp
    (((wt_cont H M).comp (continuous_mul_const h)).div (wt_cont H M) fun g => (wt_pos H M g).ne')

lemma ratio_le (H : Hyp E k) (M : ℕ) (h g : GA E k) (D : ℝ) (hD : 1 ≤ D)
    (hd : dmin (g * h) ≤ D * dmin g) : ‖((wt M (g * h) / wt M g : ℝ) : ℂ)‖ ≤ D ^ M := by
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (wt_pos H M _).le (wt_pos H M g).le), div_le_iff₀ (wt_pos H M g)]
  exact wt_le H M g h D hD hd

def Q (H : Hyp E k) (M : ℕ) (h : GA E k) : XB E k :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun g => ((wt M (g * h) / wt M g : ℝ) : ℂ))
    (ratio_cont H M h) ((H.rt h).choose ^ M) fun g =>
      ratio_le H M h g _ (H.rt h).choose_spec.1 ((H.rt h).choose_spec.2 g)

lemma norm_Q_le (H : Hyp E k) (M : ℕ) (h : GA E k) (D : ℝ) (hD : 1 ≤ D)
    (hd : ∀ g, dmin (g * h) ≤ D * dmin g) : ‖Q H M h‖ ≤ D ^ M :=
  (BoundedContinuousFunction.norm_le (pow_nonneg (zero_le_one.trans hD) M)).mpr fun g =>
    ratio_le H M h g D hD (hd g)

def rho (H : Hyp E k) (M : ℕ) : GA E k →* (XB E k →L[ℂ] XB E k) where
  toFun h := (ContinuousLinearMap.mul ℂ (XB E k) (Q H M h)).comp (Rt E k h)
  map_one' := by
    ext x g
    change ((wt M (g * 1) / wt M g : ℝ) : ℂ) * x (g * 1) = x g
    rw [mul_one, div_self (wt_pos H M g).ne', Complex.ofReal_one, one_mul]
  map_mul' h h' := by
    ext x g
    change ((wt M (g * (h * h')) / wt M g : ℝ) : ℂ) * x (g * (h * h')) =
      ((wt M (g * h) / wt M g : ℝ) : ℂ) * (((wt M (g * h * h') / wt M (g * h) : ℝ) : ℂ) * x (g * h * h'))
    rw [← mul_assoc, ← mul_assoc, ← Complex.ofReal_mul]
    congr 2
    have := (wt_pos H M (g * h)).ne'
    field_simp

lemma rho_apply (H : Hyp E k) (M : ℕ) (h g : GA E k) (x : XB E k) :
    rho H M h x g = ((wt M (g * h) / wt M g : ℝ) : ℂ) * x (g * h) := rfl

def J (H : Hyp E k) (M : ℕ) : XB E k →L[ℂ] XB E k := ContinuousLinearMap.mul ℂ (XB E k) (W H M)

lemma J_apply (H : Hyp E k) (M : ℕ) (x : XB E k) (g : GA E k) : J H M x g = (wt M g : ℂ) * x g := rfl

lemma inter (H : Hyp E k) (M : ℕ) (h : GA E k) (x : XB E k) : J H M (rho H M h x) = Rt E k h (J H M x) := by
  ext g
  rw [J_apply, rho_apply, Rt_apply, J_apply, ← mul_assoc, ← Complex.ofReal_mul]
  congr 2
  have := (wt_pos H M g).ne'
  field_simp

lemma inj (H : Hyp E k) (M : ℕ) : Function.Injective (J H M) := by
  intro x y hxy
  ext g
  have e := congrArg (fun z : XB E k => z g) hxy
  simp only [J_apply] at e
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (wt_pos H M g).ne') e

variable [_root_.NumberField.IsTotallyComplex E]

lemma smv (H : Hyp E k) (M : ℕ) (x : XB E k) (hx : SmV ((rho H M).comp (infGL E k)) x) :
    SmV (repI E k) (J H M x) := by
  have e : orb (repI E k) (J H M x) = fun A => J H M (orb ((rho H M).comp (infGL E k)) x A) := by
    funext A
    unfold orb
    split_ifs with hA
    · exact (inter H M _ x).symm
    · exact (map_zero (J H M)).symm
  unfold SmV
  rw [e]
  exact hx.continuousLinearMap_comp ((J H M).restrictScalars ℝ)

end SmoothVectorHyp

theorem secondCohomologyBound_of_boundaryBound : H0 → K1 → K2 := by
  intro hH hK E _ _ _ k hk M
  obtain ⟨h1, -, -, -, -, ⟨B, N, -, h6⟩, -⟩ := hH E k
  obtain ⟨kc, kpos, kle, -, kcpt, -⟩ := hK E k hk
  have H : SmoothVectorHyp.Hyp E k := ⟨kc, kpos, fun h => by
    obtain ⟨B, hB, hB'⟩ := kcpt {h} isCompact_singleton
    exact ⟨B, hB, hB' h rfl⟩⟩
  refine ⟨SmoothVectorHyp.rho H M, SmoothVectorHyp.J H M, ⟨fun x g => rfl, SmoothVectorHyp.inter H M, SmoothVectorHyp.inj H M, ?_⟩,
    fun x hx => SmoothVectorHyp.smv H M x hx⟩
  have hne : Nonempty {ξ : Fin k → E // ξ ≠ 0} :=
    ⟨⟨fun _ => 1, fun h => one_ne_zero (congrFun h ⟨0, hk⟩)⟩⟩
  refine ⟨max B 1 ^ M, N * M, pow_nonneg (zero_le_one.trans (le_max_right _ _)) M, fun y x => ?_⟩
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = 1 + ‖(Matrix.of.symm y.val : LieI (InfinitePlace E) k)‖ +
      ‖(Matrix.of.symm y⁻¹.val : LieI (InfinitePlace E) k)‖ := ⟨_, rfl⟩
  rw [← hP]
  have hP1 : 1 ≤ P := by
    rw [hP]
    linarith [norm_nonneg (Matrix.of.symm y.val : LieI (InfinitePlace E) k),
      norm_nonneg (Matrix.of.symm y⁻¹.val : LieI (InfinitePlace E) k)]
  have hPinv : 1 + ‖(Matrix.of.symm y⁻¹.val : LieI (InfinitePlace E) k)‖ +
      ‖(Matrix.of.symm y⁻¹⁻¹.val : LieI (InfinitePlace E) k)‖ = P := by
    rw [inv_inv, hP]; ring
  have hD : 1 ≤ max B 1 * P ^ N := one_le_mul_of_one_le_of_one_le (le_max_right _ _) (one_le_pow₀ hP1)
  have hDpos : 0 < max B 1 * P ^ N := zero_lt_one.trans_le hD
  have hd : ∀ g, dmin (g * infGL E k y) ≤ max B 1 * P ^ N * dmin g := by
    intro g
    rw [← div_le_iff₀' hDpos]
    show _ ≤ ⨅ ξ : {ξ : Fin k → E // ξ ≠ 0}, ht g ξ.1
    refine le_ciInf fun ξ => ?_
    rw [div_le_iff₀' hDpos]
    calc dmin (g * infGL E k y) ≤ ht (g * infGL E k y) ξ.1 := kle _ _ ξ.2
      _ ≤ B * (1 + ‖(Matrix.of.symm y⁻¹.val : LieI (InfinitePlace E) k)‖ +
          ‖(Matrix.of.symm y⁻¹⁻¹.val : LieI (InfinitePlace E) k)‖) ^ N *
            ht (g * infGL E k y * infGL E k y⁻¹) ξ.1 := h6 y⁻¹ _ ξ.1 ξ.2
      _ = B * P ^ N * ht g ξ.1 := by
          rw [hPinv, mul_assoc g, ← map_mul, mul_inv_cancel, map_one, mul_one]
      _ ≤ max B 1 * P ^ N * ht g ξ.1 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (zero_le_one.trans hP1) _))
            (h1 g ξ.1 ξ.2).le
  change ‖SmoothVectorHyp.Q H M (infGL E k y) * Rt E k (infGL E k y) x‖ ≤ _
  calc ‖SmoothVectorHyp.Q H M (infGL E k y) * Rt E k (infGL E k y) x‖
        ≤ ‖SmoothVectorHyp.Q H M (infGL E k y)‖ * ‖Rt E k (infGL E k y) x‖ := norm_mul_le _ _
    _ = ‖SmoothVectorHyp.Q H M (infGL E k y)‖ * ‖x‖ := by rw [norm_Rt]
    _ ≤ (max B 1 * P ^ N) ^ M * ‖x‖ :=
        mul_le_mul_of_nonneg_right (SmoothVectorHyp.norm_Q_le H M _ _ hD hd) (norm_nonneg _)
    _ = max B 1 ^ M * P ^ (N * M) * ‖x‖ := by rw [mul_pow, ← pow_mul]

end PositivityTheory.AdelicQuotientData

end
end
