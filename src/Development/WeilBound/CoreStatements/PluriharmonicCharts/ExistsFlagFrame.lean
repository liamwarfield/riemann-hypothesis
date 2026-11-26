module

public import Development.WeilBound.CoreStatements.PluriharmonicCharts.MCoordIdealLeOfHomog

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PluriharmonicCharts.MinorColsBEqZero
section -- merged from Development.WeilBound.CoreStatements.PluriharmonicCharts.MinorUpdateColLin
open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Classical

noncomputable section

namespace PositivityTheory.Xgp.W

open GlobalTheory.CompanionTheory.Ar.PB.MinorCalc

variable {N j : ℕ}

section Ring

variable {R : Type} [CommRing R]

theorem minor_self_of_lower (B : Matrix (Fin N) (Fin N) R) (S : Finset (Fin N))
    (hB : ∀ a ∈ S, ∀ c ∈ S, a < c → B a c = 0) : minorIJ B S S = ∏ c ∈ S, B c c := by
  rw [minorIJ_eq_det B S S _ rfl rfl, det_of_lowerTriangular, prod_mem_eq_prod_enum S (fun c => B c c)]
  · rfl
  · intro x y hxy
    exact hB _ (Finset.orderEmbOfFin_mem _ _ _) _ (Finset.orderEmbOfFin_mem _ _ _)
      ((S.orderEmbOfFin rfl).strictMono hxy)

theorem minor_congr_cols {A B : Matrix (Fin N) (Fin N) R} (I J : Finset (Fin N))
    (h : ∀ r, ∀ c ∈ J, A r c = B r c) : minorIJ A I J = minorIJ B I J := by
  unfold minorIJ
  split_ifs with e
  · congr 1
    ext x y
    exact h _ _ (Finset.orderEmbOfFin_mem _ _ _)
  · rfl

theorem minor_updateCol_lin (A : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)) {c : Fin N} (hc : c ∈ J)
    (β δ : R) (v w : Fin N → R) :
    minorIJ (A.updateCol c (β • v + δ • w)) I J =
      β * minorIJ (A.updateCol c v) I J + δ * minorIJ (A.updateCol c w) I J := by
  unfold minorIJ
  split_ifs with e
  · have hr : c ∈ Set.range (J.orderEmbOfFin rfl) := by rw [Finset.range_orderEmbOfFin]; exact hc
    obtain ⟨x₀, rfl⟩ := hr
    have key : ∀ u : Fin N → R, (A.updateCol (J.orderEmbOfFin rfl x₀) u).submatrix (I.orderEmbOfFin e)
        (J.orderEmbOfFin rfl) = (A.submatrix (I.orderEmbOfFin e) (J.orderEmbOfFin rfl)).updateCol x₀
          (u ∘ I.orderEmbOfFin e) := fun u => by
      ext x y
      simp only [submatrix_apply, updateCol_apply, (J.orderEmbOfFin rfl).injective.eq_iff, Function.comp]
    rw [key, key, key, show (β • v + δ • w) ∘ I.orderEmbOfFin e = β • (v ∘ I.orderEmbOfFin e) +
      δ • (w ∘ I.orderEmbOfFin e) from rfl, det_updateCol_add, det_updateCol_smul, det_updateCol_smul]
  · simp

theorem minor_swapCol (A : Matrix (Fin N) (Fin N) R) (I S : Finset (Fin N)) {ca cb : Fin N} (hca : ca ∈ S)
    (hS : ∀ c ∈ S, c ≤ ca) (hcb : ca < cb) :
    minorIJ A I (insert cb (S.erase ca)) = minorIJ (A.updateCol ca fun r => A r cb) I S := by
  have hn : cb ∉ S.erase ca := fun h => absurd (hS _ (Finset.mem_of_mem_erase h)) (not_le.2 hcb)
  have hcard : (insert cb (S.erase ca)).card = S.card := by
    rw [Finset.card_insert_of_notMem hn, Finset.card_erase_add_one hca]
  by_cases e : I.card = S.card
  · rw [minorIJ_eq_det _ _ _ _ e hcard, minorIJ_eq_det _ _ _ _ e rfl]
    have hf : (fun x => if S.orderEmbOfFin rfl x = ca then cb else S.orderEmbOfFin rfl x) =
        (insert cb (S.erase ca)).orderEmbOfFin hcard := by
      refine Finset.orderEmbOfFin_unique hcard (fun x => ?_) fun x y hxy => ?_
      · split_ifs with h
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨h, Finset.orderEmbOfFin_mem _ _ _⟩)
      · have h1 := (S.orderEmbOfFin rfl).strictMono hxy
        have h2 := hS _ (Finset.orderEmbOfFin_mem S rfl y)
        split_ifs with h h' h'
        · rw [h, h'] at h1; exact absurd h1 (lt_irrefl _)
        · rw [h] at h1; exact absurd h2 (not_le.2 h1)
        · exact (hS _ (Finset.orderEmbOfFin_mem S rfl x)).trans_lt hcb
        · exact h1
    congr 1
    ext x y
    simp only [submatrix_apply, updateCol_apply, ← hf]
    split_ifs <;> rfl
  · rw [minorIJ_of_card_ne _ e, minorIJ_of_card_ne _ (by rwa [hcard])]

theorem minor_one_of_ne {I J : Finset (Fin N)} {a : Fin N} (ha : a ∈ I) (hb : a ∉ J) :
    minorIJ (1 : Matrix (Fin N) (Fin N) R) I J = 0 :=
  minorIJ_eq_zero_of_row _ ha fun c hc => Matrix.one_apply_ne fun e => hb (e ▸ hc)

end Ring

theorem exists_rows {k : Type} [Field k] (M : Matrix (Fin N) (Fin N) k) (hM : IsBlockDiag j M) (hd : M.det ≠ 0) :
    ∃ ρ : Fin N → Fin N, (∀ a, ((ρ a : ℕ) < N - j ↔ (a : ℕ) < N - j)) ∧ ∀ b : Fin N,
      ((M.submatrix ρ id).submatrix
        (Subtype.val : {a : Fin N // a ≤ b ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)} → Fin N) Subtype.val).det ≠ 0 := by
  have main : ∀ n ≤ N, ∃ ρ : Fin N → Fin N, (∀ a, ((ρ a : ℕ) < N - j ↔ (a : ℕ) < N - j)) ∧ ∀ n' ≤ n,
      ∀ v : Fin N → k, (∀ a : Fin N, n' ≤ (a : ℕ) → v a = 0) → (∀ a : Fin N, (a : ℕ) < n' → (M *ᵥ v) (ρ a) = 0) →
        v = 0 := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨id, fun _ => Iff.rfl, fun n' hn' v hv _ => funext fun a => hv a (by omega)⟩
    | succ n ih =>
      intro hn
      obtain ⟨ρ, hρ, H⟩ := ih (by omega)
      let b : Fin N := ⟨n, by omega⟩
      by_cases hex : ∃ v : Fin N → k, (∀ a : Fin N, n + 1 ≤ (a : ℕ) → v a = 0) ∧
          (∀ a : Fin N, (a : ℕ) < n → (M *ᵥ v) (ρ a) = 0) ∧ v ≠ 0
      · obtain ⟨v, hv1, hv2, hv0⟩ := hex
        have hvb : v b ≠ 0 := fun e => hv0 (H n le_rfl v (fun a ha => by
          rcases Nat.lt_or_ge n a with h | h
          · exact hv1 a h
          · rw [show a = b from Fin.ext (le_antisymm h ha)]; exact e) hv2)
        let v' : Fin N → k := fun a => if ((a : ℕ) < N - j ↔ (b : ℕ) < N - j) then v a else 0
        have hv' : M *ᵥ v' ≠ 0 := fun e => hvb (by
          have := congrFun (Matrix.eq_zero_of_mulVec_eq_zero hd e) b
          simpa [v'] using this)
        obtain ⟨r, hr⟩ := Function.ne_iff.1 hv'
        have hrb : ((r : ℕ) < N - j ↔ (b : ℕ) < N - j) := by
          by_contra hc
          refine hr (show ∑ c, M r c * v' c = 0 from Finset.sum_eq_zero fun c _ => ?_)
          by_cases e : ((c : ℕ) < N - j ↔ (b : ℕ) < N - j)
          · show M r c * _ = 0
            rw [hM r c fun e' => hc (e'.trans e), zero_mul]
          · show _ * v' c = 0
            simp only [v', if_neg e, mul_zero]
        have hr' : (M *ᵥ v) r ≠ 0 := by
          refine fun e => hr (Eq.trans (show ∑ c, M r c * v' c = ∑ c, M r c * v c from
            Finset.sum_congr rfl fun c _ => ?_) e)
          by_cases e : ((c : ℕ) < N - j ↔ (b : ℕ) < N - j)
          · show _ * v' c = _
            simp only [v', if_pos e]
          · show M r c * _ = M r c * _
            rw [hM r c fun e' => e (e'.symm.trans hrb), zero_mul, zero_mul]
        have hup : ∀ a : Fin N, (a : ℕ) < n → Function.update ρ b r a = ρ a := fun a ha =>
          Function.update_of_ne (fun e => by rw [e] at ha; exact lt_irrefl _ ha) _ _
        refine ⟨Function.update ρ b r, fun a => ?_, fun n' hn' w hw1 hw2 => ?_⟩
        · by_cases e : a = b
          · rw [e, Function.update_self]; exact hrb
          · rw [Function.update_of_ne e]; exact hρ a
        · rcases Nat.lt_or_ge n' (n + 1) with h | h
          · exact H n' (by omega) w hw1 fun a ha => by rw [← hup a (by omega)]; exact hw2 a ha
          · obtain rfl : n' = n + 1 := by omega
            have h0 := H n le_rfl (w - (w b / v b) • v) (fun a ha => by
              rcases Nat.lt_or_ge n a with h | h
              · simp [hv1 a h, hw1 a h]
              · rw [show a = b from Fin.ext (le_antisymm h ha)]
                simp [div_mul_cancel₀ _ hvb]) fun a ha => by
              have := hw2 a (by omega)
              rw [hup a ha] at this
              rw [mulVec_sub, mulVec_smul, Pi.sub_apply, Pi.smul_apply, this, hv2 a ha, smul_zero, sub_zero]
            have h1 := sub_eq_zero.1 h0
            have h2 := hw2 b (by simp [b])
            rw [Function.update_self, h1, mulVec_smul, Pi.smul_apply, smul_eq_mul] at h2
            rw [h1, (mul_eq_zero.1 h2).resolve_right hr', zero_smul]
      · push Not at hex
        refine ⟨ρ, hρ, fun n' hn' w hw1 hw2 => ?_⟩
        rcases Nat.lt_or_ge n' (n + 1) with h | h
        · exact H n' (by omega) w hw1 hw2
        · obtain rfl : n' = n + 1 := by omega
          exact hex w hw1 fun a ha => hw2 a (by omega)
  obtain ⟨ρ, hρ, H⟩ := main N le_rfl
  refine ⟨ρ, hρ, fun b h0 => ?_⟩
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  let P : Fin N → Prop := fun a => a ≤ b ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)
  let v : Fin N → k := fun a => if h : P a then w ⟨a, h⟩ else 0
  have hv := H (b + 1) b.2 v (fun a ha => dif_neg fun h => by have : (a : ℕ) ≤ b := h.1; omega) fun a ha => by
    have e1 : (M *ᵥ v) (ρ a) = ∑ c : {c // P c}, M (ρ a) c * w c := by
      show ∑ c, M (ρ a) c * v c = _
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ P,
        Finset.sum_eq_zero (s := Finset.univ.filter fun c => ¬ P c) (fun c hc => by
          rw [show v c = 0 from dif_neg (Finset.mem_filter.1 hc).2, mul_zero]), add_zero,
        Finset.sum_subtype (p := P) _ (by simp)]
      exact Finset.sum_congr rfl fun c _ => by rw [show v c = w c from dif_pos c.2]
    rw [e1]
    by_cases e : ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)
    · exact congrFun hw ⟨a, (by omega : (a : ℕ) ≤ b), e⟩
    · exact Finset.sum_eq_zero fun c _ => by
        rw [hM _ _ fun e' => e ((hρ a).symm.trans (e'.trans c.2.2)), zero_mul]
  refine hw0 (funext fun c => ?_)
  have := congrFun hv c
  rwa [show v c = w c from dif_pos c.2] at this

theorem exists_step_of_lt (hj : j ≤ N) {r c : Fin N} (h : c < r) (hs : ((r : ℕ) < N - j ↔ (c : ℕ) < N - j)) :
    ∃ i, IsProperStep N j i ∧ c ∈ stepCols N j i ∧ ∀ a ∈ stepCols N j i, a ≤ c := by
  have h' : (c : ℕ) < r := h
  have hr := r.2
  by_cases e : (c : ℕ) < N - j
  · have := hs.2 e
    refine ⟨⟨c + j, by omega⟩, ⟨by simp only; omega, by simp only; omega⟩, ?_, fun a ha => ?_⟩
    · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [if_neg (by omega)]; omega
    · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      rw [if_neg (by omega)] at ha
      show (a : ℕ) ≤ c
      omega
  · refine ⟨⟨c - (N - j), by omega⟩, ⟨by simp only; omega, by simp only; omega⟩, ?_, fun a ha => ?_⟩
    · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [if_pos (by omega)]; omega
    · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      rw [if_pos (by omega)] at ha
      show (a : ℕ) ≤ c
      omega

theorem exists_local_frame {L : Type} [Field L] (O : Subring L) [IsLocalRing O] (hj : j ≤ N)
    (h : Matrix (Fin N) (Fin N) L) (hb : IsBlockDiag j h) (hd : h.det ≠ 0)
    (hP : ∀ i, IsProperStep N j i → ∃ η : L, η ≠ 0 ∧ (∀ I, η * minorIJ h I (stepCols N j i) ∈ O) ∧
      ∃ I, η * minorIJ h I (stepCols N j i) ≠ 0 ∧ (η * minorIJ h I (stepCols N j i))⁻¹ ∈ O) :
    ∃ b : Matrix (Fin N) (Fin N) L, IsBlockDiag j b ∧ b.BlockTriangular id ∧ (∀ a, b a a ≠ 0) ∧
      (∀ a c, (h * b) a c ∈ O) ∧ ∀ a c, (h * b)⁻¹ a c ∈ O := by
  obtain ⟨V, hV⟩ := (LocalSubring.mk O).exists_le_valuationSubring
  obtain ⟨hOV, hloc⟩ := hV
  have hOV' : ∀ s ∈ O, s ∈ V := fun s hs => hOV hs
  have dom : ∀ s ∈ O, s ≠ 0 → s⁻¹ ∈ V → s⁻¹ ∈ O := fun s hs h0 hi => by
    have hu : IsUnit (Subring.inclusion hOV ⟨s, hs⟩) :=
      IsUnit.of_mul_eq_one ⟨s⁻¹, hi⟩ (Subtype.ext (mul_inv_cancel₀ h0))
    obtain ⟨t, ht⟩ := (hloc.1 _ hu).exists_right_inv
    have ht' : s * (t : L) = 1 := congrArg Subtype.val ht
    rw [inv_eq_of_mul_eq_one_right ht']
    exact t.2
  obtain ⟨b₀, hb₀, hb₀t, hb₀d, hmem, hdet, hinv⟩ := GlobalTheory.T.block_diag_valuation_normalization L V N j h hb hd
  let Hv : Matrix (Fin N) (Fin N) V := Matrix.of fun a c => ⟨(h * b₀) a c, hmem a c⟩
  have hHv : Hv.map V.subtype = h * b₀ := by ext a c; rfl
  have hHvb : IsBlockDiag j Hv := fun a c e => Subtype.ext ((hb.mul hb₀) a c e)
  have hunit : IsUnit Hv.det := by
    have hdetc : ((Hv.det : V) : L) = (h * b₀).det := by
      have := RingHom.map_det V.subtype Hv
      rw [RingHom.mapMatrix_apply, hHv] at this
      exact this
    refine IsUnit.of_mul_eq_one (⟨_, hinv⟩ : V) (Subtype.ext ?_)
    change ((Hv.det : V) : L) * _ = 1
    rw [hdetc, mul_inv_cancel₀ hdet]
  obtain ⟨ρ, hρ, hρd⟩ := exists_rows (Hv.map (IsLocalRing.residue V)) (hHvb.map _) (by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (hunit.map _).ne_zero)
  obtain ⟨B, hB, hBt, hlo⟩ := IsBlockDiag.exists_upper (j := j) (G := Hv.submatrix ρ id)
    (fun a c e => hHvb _ _ fun e' => e ((hρ a).symm.trans e')) fun c => by
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
      exact hρd c
  let B' := B.map V.subtype
  let E : Matrix (Fin N) (Fin N) L := (1 : Matrix (Fin N) (Fin N) L).submatrix ρ id
  have hE : ∀ A : Matrix (Fin N) (Fin N) L, E * A = A.submatrix ρ id := fun A => by
    rw [show E * A = (1 * A).submatrix ρ id from by ext; rfl, one_mul]
  have hEO : ∀ a c, E a c ∈ O := fun a c => by
    show (1 : Matrix (Fin N) (Fin N) L) (ρ a) c ∈ O
    rw [Matrix.one_apply]; split_ifs
    exacts [O.one_mem, O.zero_mem]
  let H := h * (b₀ * B')
  have hHV : H = (Hv * B).map V.subtype := by rw [Matrix.map_mul, hHv, Matrix.mul_assoc]
  have hLo : IsLowerUni (E * H) := by
    have := hlo.map V.subtype
    rw [hE, hHV]
    exact this
  have hdEH : E.det * H.det = 1 := by rw [← det_mul, hLo.det]
  have hbb : IsBlockDiag j (b₀ * B') := hb₀.mul (hB.map _)
  have hbt : (b₀ * B').BlockTriangular id := hb₀t.mul (hBt.map _)
  have hbd : ∀ a, (b₀ * B') a a ≠ 0 := fun a h0 => by
    have h2 : ∏ i, (b₀ * B') i i = 0 := Finset.prod_eq_zero (Finset.mem_univ a) h0
    rw [det_mul, det_of_upperTriangular hbt, h2, mul_zero, mul_zero] at hdEH
    exact zero_ne_one hdEH
  have hEb : IsBlockDiag j E := fun a c e => isBlockDiag_one _ _ fun e' => e ((hρ a).symm.trans e')
  have hLoO : ∀ r c, (E * H) r c ∈ O := by
    intro r c
    rcases lt_trichotomy r c with e | e | e
    · rw [hLo.2 _ _ e]; exact O.zero_mem
    · rw [e, hLo.1]; exact O.one_mem
    by_cases hs : ((r : ℕ) < N - j ↔ (c : ℕ) < N - j)
    swap
    · rw [(hEb.mul (hb.mul hbb)) r c hs]; exact O.zero_mem
    obtain ⟨i, hi, hc, hmax⟩ := exists_step_of_lt hj e hs
    obtain ⟨η, hη, hO, I₀, hI₀, hI₀'⟩ := hP i hi
    set S := stepCols N j i
    let θ : L := (∏ c ∈ S, (b₀ * B') c c) / η
    have hθ : ∀ I, minorIJ H I S = θ * (η * minorIJ h I S) := fun I => by
      rw [(minors_main L N j i hj).2.2.1 h _ I hbb hbt]
      simp only [θ, S]
      field_simp
    have hA : ∀ A : Matrix (Fin N) (Fin N) L, (∀ a c, A a c ∈ O) → ∃ o ∈ O, minorIJ (A * H) S S = θ * o :=
      fun A hA => ⟨∑ I, minorIJ A S I * (η * minorIJ h I S),
        sum_mem fun I _ => O.mul_mem (CPts.minorIJ_mem O hA _ _) (hO I), by
          rw [minorIJ_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl fun I _ => by rw [hθ]; ring⟩
    have hθV : θ ∈ V := by
      have h1 : minorIJ H I₀ S ∈ V.toSubring := CPts.minorIJ_mem _ (fun a c => by rw [hHV]; exact ((Hv * B) a c).2) _ _
      rw [show θ = minorIJ H I₀ S * (η * minorIJ h I₀ S)⁻¹ by rw [hθ, mul_inv_cancel_right₀ hI₀]]
      exact V.mul_mem _ _ h1 (hOV' _ hI₀')
    have hθO : θ ∈ O := by
      obtain ⟨o, ho, e1⟩ := hA E hEO
      rw [minor_self_of_lower _ _ fun a _ c _ l => hLo.2 _ _ l, Finset.prod_eq_one fun c _ => hLo.1 c] at e1
      have e2 : o⁻¹ = θ := inv_eq_of_mul_eq_one_left e1.symm
      rw [← e2] at hθV ⊢
      exact dom o ho (right_ne_zero_of_mul_eq_one e1.symm) hθV
    obtain ⟨o, ho, e1⟩ := hA (E.updateRow c (E r)) fun a c' => by
      rw [updateRow_apply]; split_ifs <;> exact hEO _ _
    have e3 : E.updateRow c (E r) * H = (E * H).updateRow c ((E * H) r) := by
      ext a c'
      by_cases e : a = c
      · subst e; simp [Matrix.mul_apply]
      · simp [Matrix.mul_apply, updateRow_ne e]
    rw [e3, minor_self_of_lower _ _ fun a ha c' hc' l => by
      rw [updateRow_ne (fun e : a = c => absurd (hmax c' hc') (not_le.2 (e ▸ l))), hLo.2 _ _ l],
      Finset.prod_eq_single c (fun a _ ha => by rw [updateRow_ne ha, hLo.1]) (fun h => absurd hc h),
      updateRow_self] at e1
    rw [e1]
    exact O.mul_mem hθO ho
  have invO : ∀ A : Matrix (Fin N) (Fin N) L, (∀ a c, A a c ∈ O) → A.det⁻¹ ∈ O → ∀ a c, A⁻¹ a c ∈ O := by
    intro A hA hdA a c
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, adjugate_apply]
    refine O.mul_mem hdA (CPts.det_mem O fun x y => ?_)
    rw [updateRow_apply]
    split_ifs
    · rw [Pi.single_apply]; split_ifs
      exacts [O.one_mem, O.zero_mem]
    · exact hA _ _
  have hEd : E.det ≠ 0 := left_ne_zero_of_mul_eq_one hdEH
  have hEi : E.det⁻¹ ∈ O := dom _ (CPts.det_mem O hEO) hEd (by
    rw [inv_eq_of_mul_eq_one_right hdEH]
    exact CPts.det_mem V.toSubring fun a c => by rw [hHV]; exact ((Hv * B) a c).2)
  have hHO : ∀ a c, H a c ∈ O := fun a c => by
    rw [← Matrix.nonsing_inv_mul_cancel_left E H hEd.isUnit, Matrix.mul_apply]
    exact sum_mem fun x _ => O.mul_mem (invO E hEO hEi _ _) (hLoO _ _)
  refine ⟨b₀ * B', hbb, hbt, hbd, hHO, invO H hHO ?_⟩
  rw [inv_eq_of_mul_eq_one_left hdEH]
  exact CPts.det_mem O hEO

end PositivityTheory.Xgp.W
end
end

open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Classical

noncomputable section

namespace PositivityTheory.Xgp.W

open GlobalTheory.CompanionTheory.Ar.PB.MinorCalc

variable {N j : ℕ}

structure Swp (N j : ℕ) (a b ca cb : Fin N) : Prop where
  hj : j ≤ N
  hb : (b : ℕ) = a + 1
  hab : (b : ℕ) < j ∨ j ≤ (a : ℕ)
  hca : (ca : ℕ) = lastCol N j a
  hcb : (cb : ℕ) = ca + 1

theorem mem_stepCols {i c : Fin N} : c ∈ stepCols N j i ↔
    ((i : ℕ) + 1 ≤ j ∧ N - j ≤ (c : ℕ) ∧ (c : ℕ) < N - j + ((i : ℕ) + 1)) ∨ (j < (i : ℕ) + 1 ∧ (c : ℕ) < (i : ℕ) + 1 - j) := by
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs <;> omega

namespace Swp

variable {a b ca cb : Fin N} (s : Swp N j a b ca cb)
include s

theorem ca_val : ((a : ℕ) + 1 ≤ j ∧ (ca : ℕ) = N - j + a) ∨ (j ≤ a ∧ (ca : ℕ) = a - j) := by
  have := s.hca
  unfold lastCol at this
  split_ifs at this <;> omega

theorem ca_mem : ca ∈ stepCols N j a := by
  have := s.ca_val; rw [mem_stepCols]; omega

theorem le_ca (c : Fin N) (hc : c ∈ stepCols N j a) : c ≤ ca := by
  have := s.ca_val; rw [mem_stepCols] at hc; show (c : ℕ) ≤ ca; omega

theorem lt_cb : ca < cb := by have := s.hcb; show (ca : ℕ) < cb; omega

theorem cb_notMem : cb ∉ stepCols N j a := fun h => absurd (s.le_ca _ h) (not_le.2 s.lt_cb)

theorem same : ((ca : ℕ) < N - j ↔ (cb : ℕ) < N - j) := by
  have := s.ca_val; have := s.hcb; have := s.hb; have := s.hab; have := b.2; have := s.hj; omega

theorem proper : IsProperStep N j a := by
  have := s.hb; have := s.hab; have := b.2; constructor <;> omega

theorem cols_b : stepCols N j b = insert cb (stepCols N j a) := by
  ext c
  have := s.ca_val; have := s.hcb; have := s.hb; have := s.hab; have := b.2; have := s.hj
  rw [Finset.mem_insert, mem_stepCols, mem_stepCols, Fin.ext_iff]; omega

theorem cols_prev {i : Fin N} (hi : (i : ℕ) + 1 = a) (hp : IsProperStep N j i) :
    stepCols N j i = (stepCols N j a).erase ca := by
  ext c
  have := s.ca_val; have := s.hcb; have := s.hb; have := s.hab; have := b.2; have := s.hj; have := hp.1
  rw [Finset.mem_erase, mem_stepCols, mem_stepCols, Ne, Fin.ext_iff]; omega

theorem cols_first (h0 : (a : ℕ) = 0 ∨ (a : ℕ) = j) : (stepCols N j a).erase ca = ∅ := by
  ext c
  have := s.ca_val; have := s.hcb; have := s.hb; have := s.hab; have := b.2; have := s.hj
  rw [Finset.mem_erase, mem_stepCols, Ne, Fin.ext_iff]
  simp only [Finset.notMem_empty, iff_false]; omega

variable {R : Type} [CommRing R]

theorem minor_colsB (A : Matrix (Fin N) (Fin N) R) (I : Finset (Fin N)) :
    minorIJ A I (colsB N j a ca cb) = minorIJ (A.updateCol ca fun r => A r cb) I (stepCols N j a) :=
  minor_swapCol A I _ s.ca_mem s.le_ca s.lt_cb

theorem block_swap {A : Matrix (Fin N) (Fin N) R} (hA : IsBlockDiag j A) :
    IsBlockDiag j (A.updateCol ca fun r => A r cb) := fun r c h => by
  rw [updateCol_apply]
  split_ifs with e
  · exact hA r cb fun e' => h (by rw [e]; exact e'.trans s.same.symm)
  · exact hA r c h

theorem minor_colsB_eq_zero {A : Matrix (Fin N) (Fin N) R} (hA : IsBlockDiag j A) (I : Finset (Fin N))
    (hI : ¬ IsStepRows N j a I) : minorIJ A I (colsB N j a ca cb) = 0 := by
  rw [s.minor_colsB]
  exact minor_stepCols_eq_zero s.hj _ I (s.block_swap hA) hI

theorem minor_colsB_mul (g : Matrix (Fin N) (Fin N) R) {bb : Matrix (Fin N) (Fin N) R} (hbb : IsBlockDiag j bb)
    (hbt : bb.BlockTriangular id) (I : Finset (Fin N)) :
    minorIJ (g * bb) I (colsB N j a ca cb) = (∏ c ∈ (stepCols N j a).erase ca, bb c c) *
      (bb cb cb * minorIJ g I (colsB N j a ca cb) + bb ca cb * minorIJ g I (stepCols N j a)) := by
  let g' := g.updateCol ca (bb cb cb • (fun r => g r cb) + bb ca cb • fun r => g r ca)
  let b' := bb.updateCol ca fun k => if k < ca then bb k cb else if k = ca then 1 else 0
  have hb' : IsBlockDiag j b' := fun r c h => by
    simp only [b', updateCol_apply]
    split_ifs with e e' e''
    · exact hbb r cb fun e' => h (by rw [e]; exact e'.trans s.same.symm)
    · exact absurd (by rw [e, e'']) h
    · rfl
    · exact hbb r c h
  have hb't : b'.BlockTriangular id := fun r c h => by
    have h' : c < r := h
    simp only [b', updateCol_apply]
    split_ifs with e e' e''
    · exact absurd (e ▸ h') (not_lt.2 e'.le)
    · exact absurd (by rw [e, e'']) h'.ne
    · rfl
    · exact hbt h
  have e1 : minorIJ (g * bb) I (colsB N j a ca cb) = minorIJ (g' * b') I (stepCols N j a) := by
    rw [s.minor_colsB]
    refine minor_congr_cols _ _ fun r c hc => ?_
    rw [updateCol_apply, Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply]
    split_ifs with e
    · have h1 : ∀ k, g r k * bb k cb = (if k < ca then g r k * bb k cb else 0) +
          ((if k = cb then g r cb * bb cb cb else 0) + if k = ca then g r ca * bb ca cb else 0) := fun k => by
        have h2 := s.hcb
        rcases lt_trichotomy k ca with l | l | l
        · rw [if_pos l, if_neg (l.trans s.lt_cb).ne, if_neg l.ne]; ring
        · rw [if_neg (l ▸ lt_irrefl _), if_neg (l ▸ s.lt_cb.ne), if_pos l, l]; ring
        · rw [if_neg (not_lt.2 l.le), if_neg l.ne']
          by_cases e : k = cb
          · rw [if_pos e, e]; ring
          · have : cb < k := by
              have h3 : (ca : ℕ) < k := l
              have h4 : (k : ℕ) ≠ cb := fun h => e (Fin.ext h)
              show (cb : ℕ) < k
              omega
            rw [if_neg e, hbt this]; ring
      have h2 : ∀ k, g' r k * b' k c = (if k < ca then g r k * bb k cb else 0) +
          if k = ca then g r cb * bb cb cb + g r ca * bb ca cb else 0 := fun k => by
        simp only [g', b', updateCol_apply, if_pos e]
        rcases lt_trichotomy k ca with l | l | l
        · simp [l, l.ne]
        · simp [l]; ring
        · simp [not_lt.2 l.le, l.ne']
      rw [Finset.sum_congr rfl fun k _ => h1 k, Finset.sum_congr rfl fun k _ => h2 k]
      simp [Finset.sum_add_distrib]
    · refine Finset.sum_congr rfl fun k _ => ?_
      simp only [g', b', updateCol_apply, if_neg e]
      split_ifs with e'
      · rw [e', hbt (lt_of_le_of_ne (s.le_ca c hc) e), mul_zero, mul_zero]
      · rfl
  rw [e1, (minors_main R N j a s.hj).2.2.1 _ _ I hb' hb't, minor_updateCol_lin _ _ _ s.ca_mem, ← s.minor_colsB,
    updateCol_eq_self, ← Finset.mul_prod_erase _ _ s.ca_mem, mul_comm]
  have h3 : b' ca ca = 1 := by simp [b']
  rw [h3, one_mul]
  congr 1
  exact Finset.prod_congr rfl fun c hc => by simp only [b', updateCol_apply, if_neg (Finset.ne_of_mem_erase hc)]

theorem prod_xi {E : Type} [Field E] {Ψ : Type} [DecidableEq Ψ] (τ : Ψ) (f : Fin N → E) :
    ∏ i, f i ^ xiCoef τ a (τ, i) = (∏ i : Fin N, if (i : ℕ) + 1 = a then f i else 1) * f b * ((f a)⁻¹) ^ 2 := by
  have h : ∀ i, f i ^ xiCoef τ a (τ, i) = (if (i : ℕ) + 1 = a then f i else 1) * (if i = b then f b else 1) *
      if i = a then ((f a)⁻¹) ^ 2 else 1 := fun i => by
    have hb := s.hb
    simp only [xiCoef, if_true, Fin.ext_iff]
    by_cases h1 : (i : ℕ) + 1 = a
    · rw [if_pos h1, if_pos h1, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      simp
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : (i : ℕ) = a + 1
      · rw [if_pos h2, if_neg (by omega), if_pos (by omega), if_neg (by omega), show i = b from Fin.ext (by omega)]
        simp
      · rw [if_neg h2, if_neg (show ¬ (i : ℕ) = b by omega)]
        by_cases h3 : (i : ℕ) = a
        · rw [if_pos h3, if_pos h3, show i = a from Fin.ext h3]
          simp [_root_.zpow_neg, zpow_ofNat]
        · rw [if_neg h3, if_neg h3]; simp
  rw [Finset.prod_congr rfl fun i _ => h i, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp

end Swp

def facI {E : Type} [Field E] (N j : ℕ) (a : Fin N) (lam : Fin N → E) (g : Matrix (Fin N) (Fin N) E) (i : Fin N) : E :=
  if IsProperStep N j i then 1 else lam i * (if (i : ℕ) + 1 = j then
    (if (a : ℕ) < j then minorIJ g (wIdx N j) (wIdx N j) else 1) else minorIJ g (omIdx N j) (omIdx N j))

def nI {E : Type} [Field E] (N j : ℕ) (lam : Fin N → E) (T bb : Matrix (Fin N) (Fin N) E) (i : Fin N) : E :=
  if IsProperStep N j i then detFac j i T * ∏ c ∈ stepCols N j i, bb c c else lam i * detFac j i T

def muI {R : Type} [CommRing R] (N j : ℕ) (b : Fin N) (H : Matrix (Fin N) (Fin N) R) : R :=
  if IsProperStep N j b then 1 else minorIJ H (stepCols N j b) (stepCols N j b)

theorem minor_empty' {R : Type} [CommRing R] (X : Matrix (Fin N) (Fin N) R) : minorIJ X ∅ ∅ = 1 := by
  rw [minor_self_of_lower _ _ (by simp), Finset.prod_empty]

theorem cols_whole (hj : j ≤ N) {b : Fin N} (hp : ¬ IsProperStep N j b) :
    ((b : ℕ) + 1 = j ∧ stepCols N j b = wIdx N j) ∨ ((b : ℕ) + 1 ≠ j ∧ (b : ℕ) + 1 = N ∧ stepCols N j b = omIdx N j) := by
  by_cases h : (b : ℕ) + 1 = j
  · refine Or.inl ⟨h, ?_⟩
    ext c
    have := c.2
    rw [mem_stepCols]; simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and]; omega
  · have h' : (b : ℕ) + 1 = N := by by_contra h'; exact hp ⟨h, h'⟩
    refine Or.inr ⟨h, h', ?_⟩
    ext c
    rw [mem_stepCols]; simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and]; omega

theorem muI_unit {R : Type} [CommRing R] (hj : j ≤ N) (b : Fin N) {H H' : Matrix (Fin N) (Fin N) R}
    (hH : IsBlockDiag j H) (e : H' * H = 1) : muI N j b H' * muI N j b H = 1 := by
  unfold muI
  split_ifs with hp
  · exact one_mul 1
  · rcases cols_whole hj hp with ⟨-, h⟩ | ⟨-, -, h⟩
    · rw [h, ← minorIJ_mul_of_support _ _ _ _ (support_wIdx hH), e, CPts.minorIJ_one]
    · rw [h, ← minorIJ_mul_of_support _ _ _ _ (support_omIdx hH), e, CPts.minorIJ_one]

theorem Swp.alg {a b ca cb : Fin N} (s : Swp N j a b ca cb) {E : Type} [Field E] {Ψ : Type} [DecidableEq Ψ] (τ : Ψ)
    (lam : Fin N → E) {T g bb H : Matrix (Fin N) (Fin N) E} (hT : IsBlockDiag j T) (hTd : T.det ≠ 0)
    (hH : IsBlockDiag j H) (hbb : IsBlockDiag j bb) (hbt : bb.BlockTriangular id) (hbd : ∀ c, bb c c ≠ 0)
    (e : T * H = g * bb) :
    (∏ i, facI N j a lam g i ^ xiCoef τ a (τ, i)) * bb cb cb =
      muI N j b H * bb ca ca * ∏ i, nI N j lam T bb i ^ xiCoef τ a (τ, i) := by
  have hj := s.hj
  have hb := s.hb
  have hab := s.hab
  have hbN := b.2
  have hD : detFac j a T ≠ 0 := CPts.detFac_ne_zero hj a hT hTd
  set D := detFac j a T with hDdef
  set P := ∏ c ∈ (stepCols N j a).erase ca, bb c c with hPdef
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun c _ => hbd c
  have hPa : ∏ c ∈ stepCols N j a, bb c c = bb ca ca * P := (Finset.mul_prod_erase _ _ s.ca_mem).symm
  have hPb : ∏ c ∈ stepCols N j b, bb c c = bb cb cb * (bb ca ca * P) := by
    rw [s.cols_b, Finset.prod_insert s.cb_notMem, hPa]
  have hfa : facI N j a lam g a = 1 := if_pos s.proper
  have hna : nI N j lam T bb a = D * (bb ca ca * P) := by rw [nI, if_pos s.proper, hPa]
  have hDW : D = if j ≤ a then minorIJ T (wIdx N j) (wIdx N j) else 1 := by
    rw [hDdef, detFac, if_neg (show ¬ (a : ℕ) + 1 = N by omega), mul_one]
    exact if_congr (by omega) rfl rfl
  have h0 : (∏ i : Fin N, if (i : ℕ) + 1 = a then facI N j a lam g i else 1) * (D * P) =
      ∏ i : Fin N, if (i : ℕ) + 1 = a then nI N j lam T bb i else 1 := by
    by_cases ha : (a : ℕ) = 0
    · rw [Finset.prod_eq_one fun i _ => if_neg (by omega), Finset.prod_eq_one fun i _ => if_neg (by omega), hPdef,
        s.cols_first (Or.inl ha), Finset.prod_empty, hDW]
      split_ifs with h
      · rw [show wIdx N j = ∅ by
          ext c; have := c.2; simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
            iff_false]; omega, minor_empty']
        simp
      · simp
    · let i₀ : Fin N := ⟨a - 1, by omega⟩
      have hi : (i₀ : ℕ) + 1 = a := by simp only [i₀]; omega
      have hs : ∀ f : Fin N → E, (∏ i : Fin N, if (i : ℕ) + 1 = a then f i else 1) = f i₀ := fun f => by
        rw [Finset.prod_eq_single i₀ (fun i _ h => if_neg fun e => h (Fin.ext (by omega))) (by simp), if_pos hi]
      rw [hs, hs, facI, nI]
      by_cases hp : IsProperStep N j i₀
      · have := hp.1
        rw [if_pos hp, if_pos hp, s.cols_prev hi hp, one_mul, hDW, detFac, if_neg (show ¬ (i₀ : ℕ) + 1 = N by omega),
          mul_one, hi]
      · have h1 : (i₀ : ℕ) + 1 = j := by by_contra h; exact hp ⟨h, by omega⟩
        rw [if_neg hp, if_neg hp, if_pos h1, if_neg (by omega), hPdef, s.cols_first (Or.inr (by omega)),
          Finset.prod_empty, hDW, detFac, if_neg (show ¬ (i₀ : ℕ) + 1 = N by omega), hi]
        ring
  have h1 : facI N j a lam g b * (D * (bb cb cb * (bb ca ca * P))) = muI N j b H * nI N j lam T bb b := by
    rw [facI, nI, muI, ← hPb]
    by_cases hp : IsProperStep N j b
    · have := hp.1
      rw [if_pos hp, if_pos hp, if_pos hp, hDW, detFac, if_neg hp.2, mul_one]
      congr 2
      exact if_congr (by omega) rfl rfl
    · rw [if_neg hp, if_neg hp, if_neg hp, ← minorIJ_self_of_triangular bb hbt, hDW, detFac]
      rcases cols_whole hj hp with ⟨h, hc⟩ | ⟨h, h', hc⟩
      · have e1 := congrArg (fun X => minorIJ X (wIdx N j) (wIdx N j)) e
        simp only [minorIJ_mul_of_support _ _ _ _ (support_wIdx hH),
          minorIJ_mul_of_support _ _ _ _ (support_wIdx hbb)] at e1
        have e2 : (if (b : ℕ) + 1 = N then minorIJ T (omIdx N j) (omIdx N j) else 1) = 1 := by
          split_ifs with h'
          · rw [show omIdx N j = ∅ by
              ext c; simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
                iff_false]; omega, minor_empty']
          · rfl
        rw [hc, e2, if_pos h, if_pos (by omega), if_neg (by omega), if_pos (by omega)]
        linear_combination (-lam b) * e1
      · have e1 := congrArg (fun X => minorIJ X (omIdx N j) (omIdx N j)) e
        simp only [minorIJ_mul_of_support _ _ _ _ (support_omIdx hH),
          minorIJ_mul_of_support _ _ _ _ (support_omIdx hbb)] at e1
        rw [hc, if_neg h, if_pos (by omega), if_pos (by omega), if_pos h']
        linear_combination (-lam b * minorIJ T (wIdx N j) (wIdx N j)) * e1
  rw [s.prod_xi, s.prod_xi, hfa, hna, ← h0]
  have h2 := hbd ca
  have h3 := hbd cb
  have h4 : facI N j a lam g b = muI N j b H * nI N j lam T bb b / (D * (bb cb cb * (bb ca ca * P))) :=
    eq_div_of_mul_eq (by positivity) h1
  rw [h4]
  field_simp

theorem prod_xi_pair {E : Type} [Field E] {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] (τ : Ψ) (a : Fin N)
    (f : Ψ × Fin N → E) : ∏ p, f p ^ xiCoef τ a p = ∏ i, f (τ, i) ^ xiCoef τ a (τ, i) := by
  rw [Fintype.prod_prod_type, Finset.prod_eq_single τ (fun τ' _ h => Finset.prod_eq_one fun i _ => by
    simp [xiCoef, h]) (by simp)]

theorem dual_sum {R : Type} [CommRing R] {κ : Type} [Fintype κ] (i : Fin N) (u : κ → Finset (Fin N) → R)
    (u' : Finset (Fin N) → κ → R)
    (hu : ∀ I I', IsStepRows N j i I → IsStepRows N j i I' → ∑ m, u' I m * u m I' = if I = I' then 1 else 0)
    (w : Finset (Fin N) → R) (hw : ∀ I, ¬ IsStepRows N j i I → w I = 0) (I : Finset (Fin N))
    (hI : IsStepRows N j i I) : ∑ m, u' I m * ∑ I', u m I' * w I' = w I := by
  have e1 : ∑ m, u' I m * ∑ I', u m I' * w I' = ∑ I', (∑ m, u' I m * u m I') * w I' := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [mul_assoc]
  rw [e1, Finset.sum_eq_single I]
  · rw [hu I I hI hI, if_pos rfl, one_mul]
  · intro b _ hb
    by_cases hs : IsStepRows N j i b
    · rw [hu I b hI hs, if_neg (Ne.symm hb), zero_mul]
    · rw [hw b hs, mul_zero]
  · simp

theorem dual_sum' {R : Type} [CommRing R] {κ : Type} [Fintype κ] (i : Fin N) (u : κ → Finset (Fin N) → R)
    (u' : Finset (Fin N) → κ → R)
    (hu : ∀ I I', IsStepRows N j i I → IsStepRows N j i I' → ∑ m, u' I m * u m I' = if I = I' then 1 else 0)
    (H H' : Matrix (Fin N) (Fin N) R) (J J' : Finset (Fin N))
    (hw : ∀ I, ¬ IsStepRows N j i I → minorIJ H I J = 0) :
    ∑ m, (∑ I, (if IsStepRows N j i I then minorIJ H' J' I else 0) * u' I m) * ∑ I', u m I' * minorIJ H I' J =
      minorIJ (H' * H) J' J := by
  rw [minorIJ_mul]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun I _ => ?_
  split_ifs with hI
  · simp only [mul_assoc]
    rw [← Finset.mul_sum, dual_sum i u u' hu _ hw I hI]
  · simp [hw I hI]

end PositivityTheory.Xgp.W
end
end

open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Classical

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.Xgp.W

open GlobalTheory.CompanionTheory.Ar.PB.MinorCalc

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {L : Type} [Field L]
  {y : (Σ k, ι k) → Φ} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} (M : FlagModel y Ψ N j)

theorem detFac_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (i : Fin N) (T : Matrix (Fin N) (Fin N) R) :
    detFac j i (T.map f) = f (detFac j i T) := by
  unfold detFac
  rw [CPts.minorIJ_map, CPts.minorIJ_map]
  split_ifs <;> simp

theorem muI_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (i : Fin N) (T : Matrix (Fin N) (Fin N) R) :
    muI N j i (T.map f) = f (muI N j i T) := by
  unfold muI
  rw [CPts.minorIJ_map]
  split_ifs <;> simp

theorem zpow_sum' {σ : Type} (S : Finset σ) {x : L} (hx : x ≠ 0) (n : σ → ℤ) : x ^ (∑ p ∈ S, n p) = ∏ p ∈ S, x ^ n p := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ hx, ih]

theorem chartMono_ne {z : (Σ k, ι k) → L} {c : ∀ k, ι k} (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) (e : K → ℤ) :
    chartMono z c e ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hc k)

theorem chartMono_eDeg {z : (Σ k, ι k) → L} {c : ∀ k, ι k} (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) (τ : Ψ) (a : Fin N) (k₀ : K) :
    chartMono z c (eDeg M τ a k₀) * (z ⟨k₀, c k₀⟩ ^ 2 * ∏ i, chartMono z c (M.dy (τ, i)) ^ xiCoef τ a (τ, i)) = 1 := by
  rw [← prod_xi_pair τ a fun p => chartMono z c (M.dy p)]
  have e1 : ∏ p, chartMono z c (M.dy p) ^ xiCoef τ a p = ∏ k, z ⟨k, c k⟩ ^ ∑ p, xiCoef τ a p * M.dy p k := by
    simp only [chartMono, ← Finset.prod_zpow]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [zpow_sum' _ (hc k)]
    exact Finset.prod_congr rfl fun p _ => by rw [← _root_.zpow_mul, mul_comm]
  have e2 : z ⟨k₀, c k₀⟩ ^ 2 = ∏ k, z ⟨k, c k⟩ ^ (if k = k₀ then (2 : ℤ) else 0) := by
    rw [Finset.prod_eq_single k₀ (fun k _ h => by rw [ite_eq_right h, zpow_zero]) (by simp), ite_eq_left rfl, zpow_ofNat]
  rw [e1, e2, chartMono, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun k _ => ?_
  rw [← zpow_add₀ (hc k), ← zpow_add₀ (hc k), eDeg]
  rw [show -(∑ p, xiCoef τ a p * M.dy p k) - (if k = k₀ then 2 else 0) + ((if k = k₀ then 2 else 0) +
    ∑ p, xiCoef τ a p * M.dy p k) = 0 by ring, zpow_zero]

theorem chartMono_dy (z : (Σ k, ι k) → L) (c : ∀ k, ι k) (p : Ψ × Fin N) :
    chartMono z c (M.dy p) = (∏ k : NonPluckerBlocks M.blk, (z ⟨k.1, c k.1⟩ ^ M.b p k)⁻¹) *
      (M.blk p).elim 1 fun k => z ⟨k, c k⟩ := by
  rw [chartMono, ← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun k => ∀ p', M.blk p' ≠ some k)]
  congr 1
  · rw [Finset.prod_subtype (p := fun k => ∀ p', M.blk p' ≠ some k) _ (by simp)]
    refine Finset.prod_congr (by congr) fun k _ => ?_
    rw [FlagModel.dy, dite_eq_left k.2, _root_.zpow_neg]
  · cases hp : M.blk p with
    | none =>
      refine Finset.prod_eq_one fun k hk => ?_
      rw [FlagModel.dy, dite_eq_right (Finset.mem_filter.1 hk).2, hp, ite_eq_right (by simp), zpow_zero]
    | some k₁ =>
      have hk₁ : ¬ ∀ p', M.blk p' ≠ some k₁ := fun h => h p hp
      rw [Finset.prod_eq_single k₁ (fun k hk h => by
        rw [FlagModel.dy, dite_eq_right (Finset.mem_filter.1 hk).2, hp, ite_eq_right (by simpa using h.symm), zpow_zero])
        (fun h => (h (Finset.mem_filter.2 ⟨Finset.mem_univ k₁, hk₁⟩)).elim), FlagModel.dy, dite_eq_right hk₁, ite_eq_left hp,
        zpow_one]
      rfl

theorem blk_some {i : Fin N} (τ : Ψ) (hi : IsProperStep N j i) : ∃ k, M.blk (τ, i) = some k :=
  Option.ne_none_iff_exists'.1 fun h => (M.blk_none _).1 h hi

theorem isPt_base {z : (Σ k, ι k) → L} (hz : IsPt y z) : IsPt M.x (basePart M.blk z) :=
  hz.comp (CPts.blockMap_base M) (algebraMap M.Ω Φ) (funext M.y_base)

theorem hasVal_base {z : (Σ k, ι k) → L} {s : M.Ω} {v : L} (h : HasVal M.x (basePart M.blk z) s v) :
    HasVal y z (algebraMap M.Ω Φ s) v :=
  HasVal.pull (CPts.blockMap_base M) (algebraMap M.Ω Φ) (funext M.y_base) h

theorem chart_ne {z : (Σ k, ι k) → L} {F : FrameData ι Ψ N M.Ω M.blk}
    (hG : M.GoodAt F (mCoordIdeal (basePart M.blk z))) (k : NonPluckerBlocks M.blk) : z ⟨k.1, F.c k⟩ ≠ 0 := fun h =>
  hG.1 k ((mem_iff_of_homog (isMultiHomog_X _)).2 (by rw [aeval_X]; exact h))

theorem exists_flag_frame (τ : Ψ) {z : (Σ k, ι k) → L} (hz : IsPt y z) {F : FrameData ι Ψ N M.Ω M.blk}
    (hF : M.IsFrame F) (hG : M.GoodAt F (mCoordIdeal (basePart M.blk z))) :
    ∃ (b : Matrix (Fin N) (Fin N) Φ) (H H' : Matrix (Fin N) (Fin N) (regO y z)), IsBlockDiag j b ∧
      b.BlockTriangular id ∧ (∀ a, b a a ≠ 0) ∧ IsBlockDiag j H ∧ H' * H = 1 ∧
      (F.T τ).map (algebraMap M.Ω Φ) * H.map (regO y z).subtype = M.g τ * b := by
  have := isLocalRing_regO hz
  let am := algebraMap M.Ω Φ
  let h := (F.T τ)⁻¹.map am * M.g τ
  have hTh : (F.T τ).map am * h = M.g τ := CPts.map_mul_inv_map am (hF.1 τ).2 _
  have hhb : IsBlockDiag j h := (((hF.1 τ).1.inv (hF.1 τ).2.isUnit).map am).mul (M.g_block τ)
  have hhd : h.det ≠ 0 := fun e => (M.isUnit_det_g τ).ne_zero (by rw [← hTh, det_mul, e, mul_zero])
  have hu : ∀ q I, am (F.u q I) ∈ regO y z := fun q I =>
    (exists_hasVal_of_regAt (hG.2.1 q I).1).imp fun _ => hasVal_base M
  have hu' : ∀ I q, am (F.u' I q) ∈ regO y z := fun I q =>
    (exists_hasVal_of_regAt (hG.2.1 q I).2).imp fun _ => hasVal_base M
  obtain ⟨b, hb, hbt, hbd, hO, hO'⟩ := exists_local_frame (regO y z) M.j_le h hhb hhd fun i hi => by
    obtain ⟨k, hk⟩ := blk_some M τ hi
    obtain ⟨c, hc⟩ := hz.1 k
    have hyc := hz.coord_ne hc
    have hdet : am (detFac j i (F.T τ)) ≠ 0 :=
      (map_ne_zero am).2 (CPts.detFac_ne_zero M.j_le i (hF.1 τ).1 (hF.1 τ).2)
    have hE : am (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b (τ, i) k') ≠ 0 := (map_ne_zero am).2
      (Finset.prod_ne_zero_iff.2 fun k' _ => zpow_ne_zero _ (M.x_chart_ne (isPt_base M hz).le hG k'))
    let η := am (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b (τ, i) k') / (am (detFac j i (F.T τ)) * y ⟨k, c⟩)
    have rel : ∀ m, η * ∑ I, am (F.u ⟨k, m⟩ I) * minorIJ h I (stepCols N j i) = y ⟨k, m⟩ / y ⟨k, c⟩ := fun m => by
      have := CPts.frame_gen M hF (RingHom.id Φ) hk m hhb isBlockDiag_one blockTriangular_one
        (by rw [mul_one]; exact hTh)
      simp only [RingHom.id_apply, Matrix.one_apply_eq, Finset.prod_const_one, mul_one] at this
      simp only [η]
      rw [div_mul_eq_mul_div, ← this]
      exact mul_div_mul_left _ _ hdet
    have hO : ∀ I, η * minorIJ h I (stepCols N j i) ∈ regO y z := fun I => by
      by_cases hI : IsStepRows N j i I
      · set_option synthInstance.maxHeartbeats 100000 in
          rw [← dual_sum i (fun m I => am (F.u ⟨k, m⟩ I)) (fun I m => am (F.u' I ⟨k, m⟩)) (fun I I' h1 h2 => by
            have := congrArg am (hF.2.2.1 (τ, i) k hk I I' h1 h2)
            rw [map_sum] at this
            simp only [map_mul] at this
            rw [this]
            split_ifs <;> simp) (fun I => minorIJ h I (stepCols N j i))
            (fun I hI => minor_stepCols_eq_zero M.j_le h I hhb hI) I hI, Finset.mul_sum]
        refine sum_mem fun m _ => ?_
        rw [mul_left_comm, rel]
        exact mul_mem (hu' _ _) ⟨_, hasVal_ratio hz m c hc⟩
      · rw [minor_stepCols_eq_zero M.j_le h I hhb hI, mul_zero]; exact zero_mem _
    refine ⟨η, div_ne_zero hE (mul_ne_zero hdet hyc), hO, ?_⟩
    have h1 : ∑ I, (⟨_, hu ⟨k, c⟩ I⟩ : regO y z) * ⟨_, hO I⟩ = 1 := Subtype.ext (by
      have := rel c
      rw [div_self hyc, Finset.mul_sum] at this
      simp only [AddSubmonoidClass.coe_finsetSum, Subring.coe_mul, Subring.coe_one]
      rw [← this]
      exact Finset.sum_congr rfl fun I _ => by ring)
    have h2 := congrArg (valO hz) h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_one] at h2
    obtain ⟨I, -, hI⟩ := Finset.exists_ne_zero_of_sum_ne_zero (h2.trans_ne one_ne_zero)
    rw [map_mul] at hI
    have h3 := hasVal_valO hz ⟨_, hO I⟩
    exact ⟨I, h3.ne_zero hz (right_ne_zero_of_mul hI), _, h3.inv hz (right_ne_zero_of_mul hI)⟩
  have hd : (h * b).det ≠ 0 := by
    rw [det_mul, det_of_isUpperTriangular hbt]
    exact mul_ne_zero hhd (Finset.prod_ne_zero_iff.2 fun a _ => hbd a)
  let H : Matrix (Fin N) (Fin N) (regO y z) := Matrix.of fun a c => ⟨_, hO a c⟩
  let H' : Matrix (Fin N) (Fin N) (regO y z) := Matrix.of fun a c => ⟨_, hO' a c⟩
  have e1 : H.map (regO y z).subtype = h * b := by ext; rfl
  have e2 : H'.map (regO y z).subtype = (h * b)⁻¹ := by ext; rfl
  refine ⟨b, H, H', hb, hbt, hbd, fun a c e => Subtype.ext ((hhb.mul hb) a c e), ?_, ?_⟩
  · refine Matrix.map_injective (f := (regO y z).subtype) Subtype.val_injective ?_
    show (H' * H).map _ = (1 : Matrix (Fin N) (Fin N) (regO y z)).map _
    rw [Matrix.map_mul, e1, e2, Matrix.nonsing_inv_mul _ hd.isUnit, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [e1, ← Matrix.mul_assoc, hTh]

end PositivityTheory.Xgp.W
