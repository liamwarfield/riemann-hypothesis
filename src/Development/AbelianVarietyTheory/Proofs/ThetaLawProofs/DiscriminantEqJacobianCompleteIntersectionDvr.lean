module

public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LineBundlePowSectionsEqThetaLevel
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LamIsoOfDoublingPullbackEqDiagonalSq
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KosDExactGeneric
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFactorAssociatedJacobian

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KosDApplyMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

namespace GlobalTheory.KosResidueExact

theorem kosD_apply_map {k K : Type} [CommRing k] [CommRing K] (f : k →+* K) {g : ℕ} {N : ℕ → ℕ}
    (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) k) (p q : KIx g 0 N) :
    kosD (d := 0) (fun i j j' => (m i j j').map f) (fun _ => 0) p q =
      f (kosD (d := 0) m (fun _ => 0) p q) := by
  rcases p with p | a
  · rcases q with q | a
    · set_option synthInstance.maxHeartbeats 100000 in
        simp only [kosD, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp
    · exact a.elim0
  · exact a.elim0

theorem descend {k K : Type} [Field k] [Field K] [Algebra k K] {g : ℕ} {N : ℕ → ℕ}
    (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) k)
    (H : ∀ v : KIx g 0 N → K,
      (kosD (d := 0) (fun i j j' => (m i j j').map (algebraMap k K)) (fun _ => 0)).mulVec v = 0 →
      ∃ w, ∀ p, p.1 ≠ ∅ → v (.inl p) =
        (kosD (d := 0) (fun i j j' => (m i j j').map (algebraMap k K)) (fun _ => 0)).mulVec w (.inl p))
    (v : KIx g 0 N → k) (hv : (kosD (d := 0) m (fun _ => 0)).mulVec v = 0) :
    ∃ w, ∀ p, p.1 ≠ ∅ → v (.inl p) = (kosD (d := 0) m (fun _ => 0)).mulVec w (.inl p) := by
  obtain ⟨lam, hlam⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap k K)
    (LinearMap.ker_eq_bot.2 (algebraMap k K).injective)
  have hl : ∀ a, lam (algebraMap k K a) = a := fun a => LinearMap.congr_fun hlam a
  obtain ⟨w, hw⟩ := H (fun p => algebraMap k K (v p)) (by
    funext p
    have := congrArg (algebraMap k K) (congrFun hv p)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.zero_apply, map_zero] at this ⊢
    simpa only [kosD_apply_map] using this)
  refine ⟨fun q => lam (w q), fun p hp => ?_⟩
  have := congrArg lam (hw p hp)
  rw [hl] at this
  rw [this]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, map_sum, kosD_apply_map]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

theorem transport {O K : Type} [CommRing O] [CommRing K] (f : O →+* K) {g g' : ℕ} (hg : g' = g) (l n : ℕ)
    (m : Fin g → ∀ j j', Matrix (Fin ((l - j * n) ^ g)) (Fin ((l - j' * n) ^ g)) O)
    (m' : Fin g' → ∀ j j', Matrix (Fin ((l - j * n) ^ g')) (Fin ((l - j' * n) ^ g')) K)
    (hm : ∀ i j j' k k', m' i j j' k k' = f (m (i.cast hg) j j'
      (k.cast (congrArg (fun r => (l - j * n) ^ r) hg)) (k'.cast (congrArg (fun r => (l - j' * n) ^ r) hg))))
    (H : ∀ v : KIx g' 0 (fun j => (l - j * n) ^ g') → K, (kosD m' (fun _ => 0)).mulVec v = 0 →
      ∃ w, ∀ p, p.1 ≠ ∅ → v (.inl p) = (kosD (d := 0) m' (fun _ => 0)).mulVec w (.inl p)) :
    ∀ v : KIx g 0 (fun j => (l - j * n) ^ g) → K,
      (kosD (fun i j j' => (m i j j').map f) (fun _ => 0)).mulVec v = 0 →
      ∃ w, ∀ p, p.1 ≠ ∅ → v (.inl p) =
        (kosD (d := 0) (fun i j j' => (m i j j').map f) (fun _ => 0)).mulVec w (.inl p) := by
  subst hg
  have : m' = fun i j j' => (m i j j').map f := by
    funext i j j'
    ext k k'
    exact hm i j j' k k'
  subst this
  exact H

theorem main : Out.Laws → ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] (k : Type) [Field k] (f : O →+* k) (x : KeyIn O) (n l : ℕ) (s : Fin x.P.g → RR x n) (b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (m), 1 ≤ n → x.P.g * n < l → (∀ j ≤ x.P.g, IsBasis x (b j)) → IsMul x l s b m → FinZ x s → (∀ v : KIx x.P.g 0 (fun j => (l - j * n) ^ x.P.g) → k, (kosD (fun i j j' => (m i j j').map f) (fun _ => 0)).mulVec v = 0 → ∃ w, ∀ p, p.1 ≠ ∅ → v (.inl p) = (kosD (d := 0) (fun i j j' => (m i j j').map f) (fun _ => 0)).mulVec w (.inl p)) := by
  intro hL O _ _ _ k _ f x n l s b m hn hl hb hm hZ
  obtain ⟨x', φ, w, hg, s', b', m', -, -, -, hb', hm', hmm, hZ'⟩ :=
    GlobalTheory.T.exists_keyData_baseChange_sections_matrices hL O (AlgebraicClosure k) ((algebraMap k (AlgebraicClosure k)).comp f) x n l s b m hl hb hm
  have hfin : Finite (Sp (AlgebraicClosure k)) :=
    inferInstanceAs (Finite (PrimeSpectrum (AlgebraicClosure k)))
  have hc : ∀ y : x'.P.A.left, ∃ i, y ∈ x'.P.L.U i := fun y => exists_chart x'.P.isLB y
  choose c hc using hc
  have H := (GlobalTheory.T.koszul_sections_exact_algClosed_polarisedAV hL (AlgebraicClosure k) x' n l s' b' m' c hn (by rw [hg]; exact hl)
    (hZ' hfin hZ) hb' hm' hc).1
  have H' := transport ((algebraMap k (AlgebraicClosure k)).comp f) hg l n m m' hmm H
  exact descend (K := AlgebraicClosure k) (N := fun j => (l - j * n) ^ x.P.g)
    (fun i j j' => (m i j j').map f) H'

end GlobalTheory.KosResidueExact
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsCxOfFactor
open GlobalTheory.KeyKa

namespace GlobalTheory.KeyKa.KoszulTors
section Alg
variable {R : Type} [CommRing R] {g d : ℕ} {N : ℕ → ℕ}

end Alg

variable {R : Type} [CommRing R] {g d : ℕ} {N : ℕ → ℕ} in
private lemma kosD_inl_indep_ev
    (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) R) (ev ev' : ∀ j, Matrix (Fin d) (Fin (N j)) R)
    (p : (I : Finset (Fin g)) × Fin (N I.card)) (y : _root_.GlobalTheory.KeyKa.KIx g d N) :
    _root_.GlobalTheory.KeyKa.kosD m ev (.inl p) y = _root_.GlobalTheory.KeyKa.kosD m ev' (.inl p) y := by
  rcases y with q | b <;> rfl

variable {R : Type} [CommRing R] {g d : ℕ} {N : ℕ → ℕ} in
private lemma kosD_inr_eq_zero
    (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) R) (ev : ∀ j, Matrix (Fin d) (Fin (N j)) R)
    (x : _root_.GlobalTheory.KeyKa.KIx g d N) (a : Fin d) :
    _root_.GlobalTheory.KeyKa.kosD m ev x (.inr a) = 0 := by
  rcases x with p | b <;> rfl

variable {R : Type} [CommRing R] {g d : ℕ} {N : ℕ → ℕ} in
private lemma map_kosD_inl_inl {S : Type} [CommRing S] (f : R →+* S)
    (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) R) (ev : ∀ j, Matrix (Fin d) (Fin (N j)) R)
    {d' : ℕ} (e : ∀ j, Matrix (Fin d') (Fin (N j)) S) (p q : (I : Finset (Fin g)) × Fin (N I.card)) :
    f (_root_.GlobalTheory.KeyKa.kosD m ev (.inl p) (.inl q)) =
      _root_.GlobalTheory.KeyKa.kosD (fun i j j' => (m i j j').map f) e (.inl p) (.inl q) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [_root_.GlobalTheory.KeyKa.kosD, map_sum, apply_ite]

theorem _root_.GlobalTheory.KeyKa.KoszulTors.koszul_tors : ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O]
    (g d : ℕ) (N : ℕ → ℕ) (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) O)
    (ev ev₀ : ∀ j, Matrix (Fin d) (Fin (N j)) O) (Pm : Matrix (Fin d) (Fin d) O),
    _root_.GlobalTheory.KeyKa.IsCx _root_.GlobalTheory.KeyKa.kdeg (_root_.GlobalTheory.KeyKa.kosD m ev) →
    ev 0 = Pm * ev₀ 0 → Pm.det ≠ 0 → Function.Surjective (ev₀ 0).mulVec →
    (∀ v, (ev 0).mulVec v = 0 → ∃ w : Fin g → Fin (N 1) → O, v = ∑ i, (m i 0 1).mulVec (w i)) →
    (∀ v : _root_.GlobalTheory.KeyKa.KIx g 0 N → IsLocalRing.ResidueField O,
      (_root_.GlobalTheory.KeyKa.kosD (fun i j j' => (m i j j').map (IsLocalRing.residue O))
        (fun _ => 0)).mulVec v = 0 →
      ∃ w, ∀ p, p.1 ≠ ∅ → v (.inl p) = (_root_.GlobalTheory.KeyKa.kosD (d := 0)
        (fun i j j' => (m i j j').map (IsLocalRing.residue O)) (fun _ => 0)).mulVec w (.inl p)) →
    _root_.GlobalTheory.KeyKa.IsCx _root_.GlobalTheory.KeyKa.kdeg (_root_.GlobalTheory.KeyKa.kosD m ev₀) ∧
      ∃ t, _root_.GlobalTheory.KeyKa.TorsSq _root_.GlobalTheory.KeyKa.kdeg
        (_root_.GlobalTheory.KeyKa.kosD m ev₀) t := by
  intro O _ _ _ g d N m ev ev₀ Pm hcx hev hdet hsurj hker hres
  set K := _root_.GlobalTheory.KeyKa.kosD m ev with hK
  set K₀ := _root_.GlobalTheory.KeyKa.kosD m ev₀ with hK₀
  have hrow : ∀ p y, K (.inl p) y = K₀ (.inl p) y := fun p y =>
    kosD_inl_indep_ev m ev ev₀ p y
  have haug : ∀ a y, K (.inr a) y = ∑ b, Pm a b * K₀ (.inr b) y := by
    intro a y
    rcases y with ⟨I, l⟩ | c
    · by_cases hI : I = ∅
      · subst hI
        show ev 0 a l = ∑ b, Pm a b * (if (∅ : Finset (Fin g)) = ∅ then ev₀ 0 b l else 0)
        rw [hev]
        exact Matrix.mul_apply.trans (Finset.sum_congr rfl fun b _ => by rw [if_pos rfl])
      · show (if I = ∅ then ev I.card a l else 0) = ∑ b, Pm a b * (if I = ∅ then ev₀ I.card b l else 0)
        simp [hI]
    · simp [hK, hK₀, kosD_inr_eq_zero]
  have hcx₀ : _root_.GlobalTheory.KeyKa.IsCx _root_.GlobalTheory.KeyKa.kdeg K₀ := by
    refine ⟨fun x y hxy => ?_, ?_⟩
    · rcases x with p | a
      · rw [← hrow]; exact hcx.1 _ _ hxy
      · rcases y with ⟨I, l⟩ | c
        · have hI : I ≠ ∅ := by
            rintro rfl
            exact hxy rfl
          show (if I = ∅ then ev₀ I.card a l else 0) = 0
          simp [hI]
        · exact kosD_inr_eq_zero m ev₀ _ c
    · have hsq : ∀ x y, ∑ b, K x b * K b y = 0 := fun x y => by
        have := congrFun (congrFun hcx.2 x) y
        simpa [Matrix.mul_apply] using this
      ext x y
      rw [Matrix.mul_apply, Matrix.zero_apply]
      have hmid : ∀ x b, K₀ x b * K₀ b y = K₀ x b * K b y := by
        intro x b
        rcases b with q | c
        · rw [hrow]
        · have hz : K₀ x (.inr c) = 0 := kosD_inr_eq_zero m ev₀ x c
          rw [hz, zero_mul, zero_mul]
      rcases x with p | a
      · rw [← hsq (.inl p) y]
        refine Fintype.sum_congr _ _ fun b => ?_
        rw [hmid, hrow]
      · have hvec : Pm.mulVec (fun b => ∑ c, K₀ (.inr b) c * K₀ c y) = 0 := by
          ext a'
          rw [Matrix.mulVec, dotProduct, Pi.zero_apply, ← hsq (.inr a') y]
          simp only [Finset.mul_sum, haug, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Fintype.sum_congr _ _ fun c => Fintype.sum_congr _ _ fun b => ?_
          rw [mul_assoc, hmid]
        exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet hvec) a
  refine ⟨hcx₀, _root_.GlobalTheory.TorsExists.exists_torsSq O _ _root_.GlobalTheory.KeyKa.kdeg K₀ hcx₀ ?_⟩
  intro v hv
  have hz : ∀ x c, K₀ x (.inr c) = 0 := fun x c => kosD_inr_eq_zero m ev₀ x c
  have hmv : ∀ (u : _root_.GlobalTheory.KeyKa.KIx g d N → IsLocalRing.ResidueField O) y,
      (K₀.map (IsLocalRing.residue O)).mulVec u y = ∑ I : Finset (Fin g), ∑ l : Fin (N I.card),
        IsLocalRing.residue O (K₀ y (.inl ⟨I, l⟩)) * u (.inl ⟨I, l⟩) := by
    intro u y
    rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_sigma]
    simp [Matrix.map_apply, hz]
  have hmv₀ : ∀ (u : _root_.GlobalTheory.KeyKa.KIx g 0 N → IsLocalRing.ResidueField O) y,
      (_root_.GlobalTheory.KeyKa.kosD (fun i j j' => (m i j j').map (IsLocalRing.residue O))
        (fun _ => 0)).mulVec u y = ∑ I : Finset (Fin g), ∑ l : Fin (N I.card),
        _root_.GlobalTheory.KeyKa.kosD (fun i j j' => (m i j j').map (IsLocalRing.residue O))
          (fun _ => 0) y (.inl ⟨I, l⟩) * u (.inl ⟨I, l⟩) := by
    intro u y
    rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_sigma]
    simp
  have hent : ∀ (p q : (I : Finset (Fin g)) × Fin (N I.card)),
      IsLocalRing.residue O (K₀ (.inl p) (.inl q)) =
        _root_.GlobalTheory.KeyKa.kosD (fun i j j' => (m i j j').map (IsLocalRing.residue O))
          (fun _ => (0 : Matrix (Fin 0) _ _)) (.inl p) (.inl q) := fun p q =>
    map_kosD_inl_inl _ m ev₀ _ p q

  choose u0 hu0 using fun a : Fin d => IsLocalRing.residue_surjective (v (.inr a))
  obtain ⟨s, hs⟩ := hsurj u0

  choose sa hsa using fun a : Fin d => hsurj (Pi.single a 1)
  choose x hx using fun l : Fin (N 0) => IsLocalRing.residue_surjective (v (.inl ⟨∅, l⟩))
  have hc : ∀ a, IsLocalRing.residue O ((ev₀ 0).mulVec x a) = 0 := by
    intro a
    have h := congrFun hv (.inr a)
    rw [Pi.zero_apply, hmv, Finset.sum_eq_single (∅ : Finset (Fin g))] at h
    · rw [← h]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hx]
      rfl
    · intro I _ hI
      refine Finset.sum_eq_zero fun l _ => ?_
      show IsLocalRing.residue O (if I = ∅ then ev₀ I.card a l else 0) * _ = 0
      simp [hI]
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  set s' : Fin (N 0) → O := ∑ a, (ev₀ 0).mulVec x a • sa a with hs'
  have hs'ev : (ev₀ 0).mulVec s' = (ev₀ 0).mulVec x := by
    ext a
    simp [hs', Matrix.mulVec_sum, Matrix.mulVec_smul, hsa, Finset.sum_apply, Pi.single_apply]
  have hs'res : ∀ l, IsLocalRing.residue O (s' l) = 0 := by
    intro l
    simp [hs', Finset.sum_apply, hc]
  have hx'0 : (ev 0).mulVec (x - s') = 0 := by
    rw [hev, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub, hs'ev, sub_self, Matrix.mulVec_zero]
  obtain ⟨w1, hw1⟩ := hker (x - s') hx'0

  obtain ⟨w', hw'⟩ := hres (Sum.elim (fun p => v (.inl p)) (fun e => Fin.elim0 e)) (by
    ext z
    rcases z with ⟨I, l⟩ | e
    · have h := congrFun hv (.inl ⟨I, l⟩)
      rw [Pi.zero_apply, hmv] at h
      rw [hmv₀, Pi.zero_apply, ← h]
      refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun l' _ => ?_
      rw [hent]
      rfl
    · exact Fin.elim0 e)
  let wf : (I : Finset (Fin g)) → Fin (N I.card) → IsLocalRing.ResidueField O := fun I l =>
    if hI : I = ∅ then IsLocalRing.residue O (s (Fin.cast (by simp [hI]) l))
    else if I.card = 1 then
      ∑ i, (if h : I = {i} then IsLocalRing.residue O (w1 i (Fin.cast (by simp [h]) l)) else 0)
    else w' (.inl ⟨I, l⟩)
  refine ⟨Sum.elim (fun p => wf p.1 p.2) (fun _ => 0), ?_⟩
  ext y
  rcases y with ⟨I, l⟩ | a
  · by_cases hI : I = ∅
    · subst hI
      obtain ⟨l, rfl⟩ : ∃ l' : Fin (N 0), l' = l := ⟨l, rfl⟩
      have hxl : IsLocalRing.residue O (x l) = ∑ i, ∑ l'' : Fin (N 1),
          IsLocalRing.residue O (m i 0 1 l l'') * IsLocalRing.residue O (w1 i l'') := by
        calc IsLocalRing.residue O (x l)
            = IsLocalRing.residue O ((∑ i, (m i 0 1).mulVec (w1 i)) l) := by
              rw [← hw1]
              show _ = IsLocalRing.residue O (x l - s' l)
              simp [hs'res]
          _ = _ := by simp [Finset.sum_apply, Matrix.mulVec, dotProduct, map_sum]
      refine Eq.trans ?_ (hx l)
      rw [hmv, hxl]
      have hJ : ∀ J : Finset (Fin g), ∑ l' : Fin (N J.card),
          IsLocalRing.residue O (K₀ (.inl ⟨∅, l⟩) (.inl ⟨J, l'⟩)) *
            Sum.elim (fun p : (I : Finset (Fin g)) × Fin (N I.card) => wf p.1 p.2)
              (fun _ : Fin d => (0 : IsLocalRing.ResidueField O)) (.inl ⟨J, l'⟩) =
          ∑ i, if J = {i} then ∑ l'' : Fin (N 1),
            IsLocalRing.residue O (m i 0 1 l l'') * IsLocalRing.residue O (w1 i l'') else 0 := by
        intro J
        by_cases h : ∃ i, J = {i}
        · obtain ⟨i, rfl⟩ := h
          rw [Finset.sum_eq_single i (fun j _ hj => if_neg fun h' => hj (Finset.singleton_inj.mp h').symm)
            (fun h' => absurd (Finset.mem_univ _) h'), if_pos rfl]
          refine Finset.sum_congr rfl fun l' _ => ?_
          congr 1
          · rw [hK₀]
            first
              | (simp [_root_.GlobalTheory.KeyKa.kosD]; done)
              | (simp [_root_.GlobalTheory.KeyKa.kosD]; rfl)
          · first
              | (simp [wf]; done)
              | (simp [wf]; rfl)
        · push_neg at h
          rw [Finset.sum_eq_zero fun i _ => if_neg (h i)]
          refine Finset.sum_eq_zero fun l' _ => ?_
          rw [hK₀]
          simp [_root_.GlobalTheory.KeyKa.kosD, h]
      rw [Finset.sum_congr rfl fun J _ => hJ J, Finset.sum_comm]
      simp
    · refine Eq.trans ?_ (hw' ⟨I, l⟩ hI).symm
      rw [hmv, hmv₀]
      refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun l' _ => ?_
      by_cases hdeg : J.card = I.card + 1
      · have hJ0 : J ≠ ∅ := by
          rintro rfl
          simp at hdeg
        have hJ1 : J.card ≠ 1 := by
          intro h
          exact hI (Finset.card_eq_zero.mp (by omega))
        rw [hent]
        congr 1
        simp [wf, hJ0, hJ1]
      · have h0 : K₀ (.inl ⟨I, l⟩) (.inl ⟨J, l'⟩) = 0 :=
          hcx₀.1 _ _ (by show J.card + 1 ≠ I.card + 1 + 1; omega)
        rw [← hent, h0, map_zero, zero_mul, zero_mul]
  · rw [hmv, Finset.sum_eq_single (∅ : Finset (Fin g))]
    · rw [← hu0 a, ← hs]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      show IsLocalRing.residue O (if (∅ : Finset (Fin g)) = ∅ then ev₀ 0 a l else 0) * wf ∅ l = _
      first
        | (simp [wf]; done)
        | (simp [wf]; rfl)
        | rfl
        | (simp only [wf, ↓reduceDIte, ↓reduceIte]; rfl)
    · intro I _ hI
      refine Finset.sum_eq_zero fun l _ => ?_
      show IsLocalRing.residue O (if I = ∅ then ev₀ I.card a l else 0) * _ = 0
      simp [hI]
    · intro h'
      exact absurd (Finset.mem_univ _) h'

end GlobalTheory.KeyKa.KoszulTors
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsPowSpanXLeOfDense
open GlobalTheory.KeyKa

namespace GlobalTheory.KeyKa

theorem exists_pow_span_X_le_of_dense (K : Type) [Field K] (g N : ℕ)
    (I : Ideal (MvPowerSeries (Fin g) K)) (ρ : Fin N → MvPowerSeries (Fin g) K)
    (h : ∀ (r : ℕ) (G : MvPowerSeries (Fin g) K), ∃ v : Fin N → K,
      G - ∑ k, v k • ρ k ∈ I ⊔ Ideal.span (Set.range MvPowerSeries.X) ^ r) :
    ∃ r : ℕ, Ideal.span (Set.range (MvPowerSeries.X : Fin g → MvPowerSeries (Fin g) K)) ^ r ≤ I := by
  set J : Ideal (MvPowerSeries (Fin g) K) := Ideal.span (Set.range MvPowerSeries.X) with hJ
  let L : (Fin N → K) →ₗ[K] MvPowerSeries (Fin g) K := Fintype.linearCombination K ρ
  have hL : ∀ v, L v = ∑ k, v k • ρ k := fun v => Fintype.linearCombination_apply K ρ v
  let V : ℕ →o (Submodule K (Fin N → K))ᵒᵈ :=
    ⟨fun r => OrderDual.toDual (((I ⊔ J ^ r).restrictScalars K).comap L), by
      intro a b hab
      change ((I ⊔ J ^ b).restrictScalars K).comap L ≤ ((I ⊔ J ^ a).restrictScalars K).comap L
      intro v hv
      exact (sup_le_sup_left (Ideal.pow_le_pow_right hab) I) hv⟩
  obtain ⟨r, hr⟩ := IsArtinian.monotone_stabilizes V
  have hV : ∀ v, L v ∈ I ⊔ J ^ r → L v ∈ I ⊔ J ^ (r + 1) := by
    intro v hv
    have e : ((I ⊔ J ^ r).restrictScalars K).comap L = ((I ⊔ J ^ (r + 1)).restrictScalars K).comap L :=
      hr (r + 1) (Nat.le_succ r)
    have : v ∈ ((I ⊔ J ^ r).restrictScalars K).comap L := hv
    rw [e] at this
    exact this
  have hfg : J.FG := Submodule.fg_span (Set.finite_range _)
  have hjac : J ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, hJ, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp only [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      MvPowerSeries.isUnit_iff_constantCoeff]
    simp
  refine ⟨r, Submodule.le_of_le_smul_of_le_jacobson_bot (N' := J ^ r) (N := I) (I := J)
    (Ideal.FG.pow hfg) hjac ?_⟩
  intro G hG
  obtain ⟨v, hv⟩ := h (r + 1) G
  rw [← hL] at hv
  have h1 : L v ∈ I ⊔ J ^ r := by
    have h2 : G - L v ∈ I ⊔ J ^ r :=
      (sup_le_sup_left (Ideal.pow_le_pow_right (Nat.le_succ r)) I) hv
    have h3 : G ∈ I ⊔ J ^ r := Ideal.mem_sup_right hG
    simpa using Ideal.sub_mem _ h3 h2
  have h4 := Ideal.add_mem _ hv (hV v h1)
  rw [sub_add_cancel, pow_succ'] at h4
  exact h4

theorem exists_sub_mem_of_dense : ∀ (K : Type) [Field K] (g N : ℕ) (Y : Type) [Finite Y] (I : Y → Ideal (MvPowerSeries (Fin g) K)) (ρ : Y → Fin N → MvPowerSeries (Fin g) K), (∀ (r : ℕ) (G : Y → MvPowerSeries (Fin g) K), ∃ v : Fin N → K, ∀ y, G y - ∑ k, v k • ρ y k ∈ I y ⊔ Ideal.span (Set.range MvPowerSeries.X) ^ r) → ∀ G : Y → MvPowerSeries (Fin g) K, ∃ v : Fin N → K, ∀ y, G y - ∑ k, v k • ρ y k ∈ I y := by
  intro K _ g N Y _ I ρ h G
  have hy : ∀ y, ∃ r : ℕ,
      Ideal.span (Set.range (MvPowerSeries.X : Fin g → MvPowerSeries (Fin g) K)) ^ r ≤ I y :=
    fun y => exists_pow_span_X_le_of_dense K g N (I y) (ρ y) fun r F => by
      obtain ⟨v, hv⟩ := h r (fun _ => F)
      exact ⟨v, hv y⟩
  choose r hr using hy
  obtain ⟨R, hR⟩ := (Set.finite_range r).bddAbove
  obtain ⟨v, hv⟩ := h R G
  refine ⟨v, fun y => ?_⟩
  exact (sup_le le_rfl ((Ideal.pow_le_pow_right (hR ⟨y, rfl⟩)).trans (hr y))) (hv y)

end GlobalTheory.KeyKa
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MulVecCongrDeg
open GlobalTheory.KeyKa
noncomputable section
namespace GlobalTheory.KeyKa.KosKer
open Matrix

theorem mulVec_congr_deg {R Ix : Type} [CommRing R] [Fintype Ix] {deg : Ix → ℕ} {D : Matrix Ix Ix R}
    (h : ∀ p q, deg q ≠ deg p + 1 → D p q = 0) (u u' : Ix → R) (p : Ix)
    (hu : ∀ q, deg q = deg p + 1 → u q = u' q) : (D *ᵥ u) p = (D *ᵥ u') p := by
  simp only [mulVec, dotProduct]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases hq : deg q = deg p + 1
  · rw [hu q hq]
  · rw [h p q hq, zero_mul, zero_mul]

theorem clear_denom {O Ix : Type} [CommRing O] [IsDomain O] [Fintype Ix] (D : Matrix Ix Ix O)
    (h : ∀ v, (D.map (algebraMap O (FractionRing O))) *ᵥ v = 0 →
      ∃ w, (D.map (algebraMap O (FractionRing O))) *ᵥ w = v) (x : Ix → O) (hx : D *ᵥ x = 0) :
    ∃ c : O, c ≠ 0 ∧ ∃ u, D *ᵥ u = c • x := by
  have hm : ∀ y : Ix → O, (D.map (algebraMap O (FractionRing O))) *ᵥ (algebraMap O (FractionRing O) ∘ y) =
      algebraMap O (FractionRing O) ∘ (D *ᵥ y) := fun y => funext fun p => (RingHom.map_mulVec _ D y p).symm
  obtain ⟨w, hw⟩ := h (algebraMap O (FractionRing O) ∘ x) (by rw [hm, hx]; ext p; simp)
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) w
  choose u hu using hb
  refine ⟨b, nonZeroDivisors.coe_ne_zero b, u, funext fun p => ?_⟩
  apply IsFractionRing.injective O (FractionRing O)
  have e : algebraMap O (FractionRing O) ∘ u = (b : O) • w := funext hu
  have e2 := congrFun (hm u) p
  rw [e, mulVec_smul, hw] at e2
  simp only [Function.comp, Pi.smul_apply] at e2 ⊢
  rw [← e2, smul_eq_mul, map_mul, Algebra.smul_def]

variable {g d : ℕ} {N : ℕ → ℕ}

theorem mulVec_empty {R : Type} [CommRing R] (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) R)
    (ev : ∀ j, Matrix (Fin d) (Fin (N j)) R) (u : KIx g d N → R) (a : Fin (N 0)) :
    (kosD m ev *ᵥ u) (.inl ⟨∅, a⟩) = (∑ i, m i 0 1 *ᵥ (fun k => u (.inl ⟨{i}, k⟩))) a := by
  simp only [mulVec, dotProduct, Fintype.sum_sum_type, kosD, zero_mul, Finset.sum_const_zero, add_zero,
    Finset.sum_mul, Finset.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_sigma, Finset.sum_eq_single {i}]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [if_pos ⟨by simp, by simp⟩]
    simp
    rfl
  · intro J _ hJ
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [if_neg (fun h => hJ (by simpa using h.2)), zero_mul]
  · simp

theorem mulVec_inr {R : Type} [CommRing R] (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) R)
    (ev : ∀ j, Matrix (Fin d) (Fin (N j)) R) (u : KIx g d N → R) (a : Fin d) :
    (kosD m ev *ᵥ u) (.inr a) = (ev 0 *ᵥ (fun k => u (.inl ⟨∅, k⟩))) a := by
  simp only [mulVec, dotProduct, Fintype.sum_sum_type, kosD, zero_mul, Finset.sum_const_zero, add_zero]
  rw [Fintype.sum_sigma, Finset.sum_eq_single ∅]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [if_pos rfl]
    rfl
  · intro J _ hJ
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [if_neg hJ, zero_mul]
  · simp

theorem mulVec_inl_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {d' : ℕ}
    (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) R)
    (ev : ∀ j, Matrix (Fin d) (Fin (N j)) R) (ev' : ∀ j, Matrix (Fin d') (Fin (N j)) S)
    (u : KIx g d N → R) (u' : KIx g d' N → S) (hu : ∀ q, u' (.inl q) = f (u (.inl q))) (p) :
    (kosD (fun i j j' => (m i j j').map f) ev' *ᵥ u') (.inl p) = f ((kosD m ev *ᵥ u) (.inl p)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [mulVec, dotProduct, Fintype.sum_sum_type, kosD, zero_mul, Finset.sum_const_zero, add_zero,
    map_sum, map_mul, hu, apply_ite f, map_zero, map_pow, map_neg, map_one, Matrix.map_apply]

theorem div_unif {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) O) (ev : ∀ j, Matrix (Fin d) (Fin (N j)) O)
    (hD : IsCx kdeg (kosD m ev))
    (hk : ∀ v : KIx g 0 N → IsLocalRing.ResidueField O,
      (kosD (fun i j j' => (m i j j').map (IsLocalRing.residue O)) (fun _ => 0)).mulVec v = 0 →
      ∃ w, ∀ p, p.1 ≠ ∅ → v (.inl p) =
        (kosD (d := 0) (fun i j j' => (m i j j').map (IsLocalRing.residue O)) (fun _ => 0)).mulVec w (.inl p))
    {π : O} (hπ : Irreducible π) (v : Fin (N 0) → O) (u : KIx g d N → O)
    (hu : ∀ a, π * v a = (kosD m ev *ᵥ u) (.inl ⟨∅, a⟩)) :
    ∃ y : KIx g d N → O, ∀ a, v a = (kosD m ev *ᵥ y) (.inl ⟨∅, a⟩) := by
  classical
  have hres : ∀ x : O, IsLocalRing.residue O x = 0 ↔ π ∣ x := fun x => by
    rw [IsLocalRing.residue_eq_zero_iff, hπ.maximalIdeal_eq, Ideal.mem_span_singleton]
  let u' : KIx g d N → O := fun q => if kdeg q = 2 then u q else 0
  have h1 : ∀ a : Fin (N 0), (kosD m ev *ᵥ u') (.inl ⟨∅, a⟩) = π * v a := fun a => by
    rw [hu a]
    exact mulVec_congr_deg hD.1 _ _ _ fun q hq => if_pos hq
  obtain ⟨wb, hwb⟩ := hk (Sum.elim (fun q => IsLocalRing.residue O (u' (.inl q))) 0) (by
    ext p
    rcases p with ⟨I, a⟩ | a
    · rw [mulVec_inl_map (IsLocalRing.residue O) m ev _ u' _ (fun _ => rfl)]
      by_cases hI : I = ∅
      · subst hI
        rw [h1 a]
        exact (hres _).2 (dvd_mul_right _ _)
      · rw [mulVec_congr_deg hD.1 u' 0 _ fun q hq => if_neg ?_]
        · simp
        · have : I.card ≠ 0 := by simpa using hI
          rw [hq]
          simp only [kdeg]
          omega
    · exact a.elim0)
  choose w0 hw0 using fun q => IsLocalRing.residue_surjective (R := O) (wb (.inl q))
  let w : KIx g d N → O := Sum.elim w0 0
  have h2 : ∀ q : KIx g d N, ∃ y, kdeg q = 2 → (u' - kosD m ev *ᵥ w) q = π * y := by
    rintro (p | a)
    · by_cases hp : p.1 = ∅
      · refine ⟨0, fun h => ?_⟩
        simp [kdeg, hp] at h
      · have e := hwb p hp
        rw [mulVec_inl_map (IsLocalRing.residue O) m ev _ w _ (fun q => (hw0 q).symm)] at e
        obtain ⟨y, hy⟩ := (hres ((u' - kosD m ev *ᵥ w) (.inl p))).1 (by
          rw [Pi.sub_apply, map_sub, ← e]; exact sub_self _)
        exact ⟨y, fun _ => hy⟩
    · exact ⟨0, fun h => by simp [kdeg] at h⟩
  choose y hy using h2
  refine ⟨y, fun a => mul_left_cancel₀ hπ.ne_zero ?_⟩
  have e := mulVec_congr_deg hD.1 (u' - kosD m ev *ᵥ w) (π • y) (.inl ⟨∅, a⟩) fun q hq => hy q hq
  rw [mulVec_sub, mulVec_mulVec, hD.2, zero_mulVec, sub_zero, mulVec_smul, h1 a] at e
  exact e

theorem ker_and_image : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (g d : ℕ) (N : ℕ → ℕ) (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) O) (ev : ∀ j, Matrix (Fin d) (Fin (N j)) O), IsCx kdeg (kosD m ev) → (∀ v, ((kosD m ev).map (algebraMap O (FractionRing O))).mulVec v = 0 → ∃ w, ((kosD m ev).map (algebraMap O (FractionRing O))).mulVec w = v) → (∀ v : KIx g 0 N → IsLocalRing.ResidueField O, (kosD (fun i j j' => (m i j j').map (IsLocalRing.residue O)) (fun _ => 0)).mulVec v = 0 → ∃ w, ∀ p, p.1 ≠ ∅ → v (.inl p) = (kosD (d := 0) (fun i j j' => (m i j j').map (IsLocalRing.residue O)) (fun _ => 0)).mulVec w (.inl p)) → (∀ v, (ev 0).mulVec v = 0 → ∃ w : Fin g → Fin (N 1) → O, v = ∑ i, (m i 0 1).mulVec (w i)) ∧ ∃ c : O, c ≠ 0 ∧ ∀ t, ∃ v, (ev 0).mulVec v = c • t := by
  intro O _ _ _ g d N m ev hD hK hk
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hpow : ∀ (n : ℕ) (v : Fin (N 0) → O), (∃ u : KIx g d N → O, ∀ a, π ^ n * v a = (kosD m ev *ᵥ u) (.inl ⟨∅, a⟩)) →
      ∃ y : KIx g d N → O, ∀ a, v a = (kosD m ev *ᵥ y) (.inl ⟨∅, a⟩) := by
    intro n
    induction n with
    | zero => intro v h; simpa using h
    | succ n ih =>
      rintro v ⟨u, hu⟩
      exact ih v (div_unif m ev hD hk hπ (fun a => π ^ n * v a) u fun a => by rw [← hu a]; ring)
  refine ⟨fun v hv => ?_, ?_⟩
  · let x : KIx g d N → O := Sum.elim (fun p => if h : p.1 = ∅ then v (Fin.cast (by rw [h]; rfl) p.2) else 0) 0
    have hx0 : ∀ a : Fin (N 0), x (.inl ⟨∅, a⟩) = v a := fun a => by
      simp only [x, Sum.elim_inl, dif_pos]
      rfl
    have hx : kosD m ev *ᵥ x = 0 := by
      ext p
      rcases p with p | a
      · rw [mulVec_congr_deg hD.1 x 0 _ ?_]
        · simp
        · rintro (q | q) hq
          · refine dif_neg fun h => ?_
            simp [kdeg, h] at hq
          · rfl
      · rw [mulVec_inr, funext hx0, hv]
        rfl
    obtain ⟨c, hc, u, hu⟩ := clear_denom _ hK x hx
    obtain ⟨n, e, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hπ
    obtain ⟨y, hy⟩ := hpow n v ⟨(↑e⁻¹ : O) • u, fun a => by
      rw [mulVec_smul, hu, smul_smul, ← mul_assoc, Units.inv_mul, one_mul, Pi.smul_apply, hx0, smul_eq_mul]⟩
    exact ⟨fun i k => y (.inl ⟨{i}, k⟩), funext fun a => (hy a).trans (mulVec_empty m ev y a)⟩
  · have h1 : ∀ a : Fin d, ∃ c : O, c ≠ 0 ∧ ∃ v, ev 0 *ᵥ v = c • (Pi.single a 1 : Fin d → O) := by
      intro a
      obtain ⟨c, hc, u, hu⟩ := clear_denom _ hK (Sum.elim 0 (Pi.single a 1)) (by
        ext p
        rcases p with p | p <;> simp [mulVec, dotProduct, Fintype.sum_sum_type, kosD])
      refine ⟨c, hc, fun k => u (.inl ⟨∅, k⟩), funext fun b => ?_⟩
      rw [← mulVec_inr m ev u b, hu]
      rfl
    choose c hc v hv using h1
    refine ⟨∏ a, c a, Finset.prod_ne_zero_iff.2 fun a _ => hc a, fun t => ?_⟩
    choose e he using fun a => Finset.dvd_prod_of_mem c (Finset.mem_univ a)
    refine ⟨∑ a, (t a * e a) • v a, ?_⟩
    rw [mulVec_sum]
    ext b
    simp only [mulVec_smul, hv, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [he b]
    ring

end GlobalTheory.KeyKa.KosKer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SpanModEquationsLift
open GlobalTheory.KeyKa

namespace GlobalTheory.SeriesNakayama

theorem mem_pow_smul_top_iff {O M : Type*} [CommRing O] [AddCommGroup M] [Module O M] (π : O)
    (n : ℕ) (x : M) :
    x ∈ (Ideal.span {π} ^ n • ⊤ : Submodule O M) ↔ ∃ y : M, π ^ n • y = x := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp

theorem mem_pow_smul_top_pi {O ι : Type*} [CommRing O] (π : O) (n : ℕ) (x : ι → O) :
    x ∈ (Ideal.span {π} ^ n • ⊤ : Submodule O (ι → O)) ↔
      ∀ i, x i ∈ (Ideal.span {π} ^ n • ⊤ : Submodule O O) := by
  simp only [mem_pow_smul_top_iff]
  refine ⟨fun ⟨y, hy⟩ i => ⟨y i, congrFun hy i⟩, fun h => ?_⟩
  choose y hy using h
  exact ⟨y, funext hy⟩

theorem surjective_of_mod {O ι κ : Type*} [CommRing O] (π : O)
    [IsAdicComplete (Ideal.span {π}) O] (Φ : (ι → O) →ₗ[O] (κ → O))
    (h : ∀ G : κ → O, ∃ x, ∀ j, G j - Φ x j ∈ Ideal.span {π}) : Function.Surjective Φ := by
  have : IsPrecomplete (Ideal.span {π}) (ι → O) := by
    refine ⟨fun u hu => ?_⟩
    have h1 : ∀ i, ∃ L : O, ∀ k, u k i ≡ L [SMOD (Ideal.span {π} ^ k • ⊤ : Submodule O O)] :=
      fun i => IsPrecomplete.prec' (fun k => u k i) fun {a b} hab =>
        SModEq.sub_mem.2 ((mem_pow_smul_top_pi π a _).1 (SModEq.sub_mem.1 (hu hab)) i)
    choose L hL using h1
    exact ⟨L, fun k => SModEq.sub_mem.2
      ((mem_pow_smul_top_pi π k _).2 fun i => SModEq.sub_mem.1 (hL i k))⟩
  have : IsHausdorff (Ideal.span {π}) (κ → O) := by
    refine ⟨fun x hx => funext fun j => IsHausdorff.haus' (I := Ideal.span {π}) (x j) fun n => ?_⟩
    exact SModEq.sub_mem.2 ((mem_pow_smul_top_pi π n _).1 (SModEq.sub_mem.1 (hx n)) j)
  refine surjective_of_mkQ_comp_surjective (I := Ideal.span {π}) fun G => ?_
  obtain ⟨G, rfl⟩ := Submodule.Quotient.mk_surjective _ G
  obtain ⟨x, hx⟩ := h G
  refine ⟨x, ((Submodule.Quotient.eq _).2 ?_).symm⟩
  have := (mem_pow_smul_top_pi π 1 (G - Φ x)).2 fun j => by simpa using hx j
  rwa [pow_one] at this

theorem exists_projection {O K : Type*} [CommRing O] [IsLocalRing O] [Field K] (f : O →+* K)
    (hf : RingHom.ker f = IsLocalRing.maximalIdeal O) :
    ∃ (μ : K →+ K) (l : K → O), (∀ a, f (l a) = μ a) ∧ (∀ a o, μ (a * f o) = μ a * f o) ∧
      ∀ o, μ (f o) = f o := by
  let φ : IsLocalRing.ResidueField O →+* K :=
    Ideal.Quotient.lift _ f fun a ha => by rwa [← hf] at ha
  have hφ : ∀ o, φ (IsLocalRing.residue O o) = f o := fun _ => rfl
  letI := φ.toAlgebra
  obtain ⟨r, hr⟩ := (Algebra.linearMap (IsLocalRing.ResidueField O) K).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 φ.injective)
  choose l hl using fun a => IsLocalRing.residue_surjective (R := O) (r a)
  refine ⟨φ.toAddMonoidHom.comp r.toAddMonoidHom, l, fun a => ?_, fun a o => ?_, fun o => ?_⟩
  · change _ = φ (r a)
    rw [← hl, hφ]
  · change φ (r _) = φ (r a) * _
    have : a * f o = IsLocalRing.residue O o • a := mul_comm _ _
    rw [this, map_smul, smul_eq_mul, map_mul, hφ, mul_comm]
  · change φ (r _) = _
    have : r (f o) = IsLocalRing.residue O o := LinearMap.congr_fun hr (IsLocalRing.residue O o)
    rw [this, hφ]

theorem span_mod_equations_lift (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (K : Type) [Field K] (f : O →+* K) (g N : ℕ)
    (Y : Type) (F : Y → Fin g → (MvPowerSeries (Fin g) O))
    (ρ : Y → Fin N → (MvPowerSeries (Fin g) O))
    (hf : RingHom.ker f = IsLocalRing.maximalIdeal O)
    (h : ∀ G : Y → MvPowerSeries (Fin g) K, ∃ v : Fin N → K, ∀ y,
      G y - ∑ k, v k • MvPowerSeries.map f (ρ y k) ∈
        Ideal.span (Set.range fun i => MvPowerSeries.map f (F y i)))
    (G : Y → (MvPowerSeries (Fin g) O)) :
    ∃ v : Fin N → O, ∀ y, G y - ∑ k, v k • ρ y k ∈ Ideal.span (Set.range (F y)) := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hm := hπ.maximalIdeal_eq
  have : IsAdicComplete (Ideal.span {π}) O := hm ▸ ‹_›
  obtain ⟨μ, l, hl, hμ, hμ1⟩ := exists_projection f hf
  let Φ : (Fin N ⊕ (Y × Fin g × (Fin g →₀ ℕ)) → O) →ₗ[O] (Y × (Fin g →₀ ℕ) → O) :=
    { toFun := fun x j => ∑ k, x (.inl k) * MvPowerSeries.coeff j.2 (ρ j.1 k) +
        ∑ i, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal j.2,
          x (.inr (j.1, i, p.1)) * MvPowerSeries.coeff p.2 (F j.1 i)
      map_add' := fun x x' => funext fun j => by
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
        ring
      map_smul' := fun c x => funext fun j => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_add, Finset.mul_sum,
          mul_assoc] }
  have hΦ : Function.Surjective Φ := by
    refine surjective_of_mod π Φ fun G => ?_
    let G' : Y → MvPowerSeries (Fin g) K := fun y d => f (G (y, d))
    obtain ⟨v, hv⟩ := h G'
    choose H hH using fun y => (Ideal.mem_span_range_iff_exists_fun).1 (hv y)
    refine ⟨Sum.elim (fun k => l (v k)) fun q => l (MvPowerSeries.coeff q.2.2 (H q.1 q.2.1)), ?_⟩
    rintro ⟨y, d⟩
    rw [← hm, ← hf, RingHom.mem_ker]
    have h1 := congrArg (fun s => μ (MvPowerSeries.coeff d s)) (eq_sub_iff_add_eq.1 (hH y))
    have h2 : MvPowerSeries.coeff d (G' y) = f (G (y, d)) := rfl
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_sum, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_map,
      MvPowerSeries.coeff_smul, hμ, hμ1, h2] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, map_sub, map_add (f := _), map_sum, map_mul, Sum.elim_inl,
      Sum.elim_inr, hl]
    rw [← h1, add_comm, sub_self]
  obtain ⟨x, hx⟩ := hΦ fun j => MvPowerSeries.coeff j.2 (G j.1)
  refine ⟨fun k => x (.inl k), fun y => Ideal.mem_span_range_iff_exists_fun.2
    ⟨fun i => (show MvPowerSeries (Fin g) O from fun d => x (.inr (y, i, d))), ?_⟩⟩
  ext d
  have h1 : _ = MvPowerSeries.coeff d (G y) := congrFun hx (y, d)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sub, map_sum, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_smul, ← h1, Φ,
    LinearMap.coe_mk, AddHom.coe_mk, add_sub_cancel_left]
  exact Finset.sum_congr rfl fun i _ => MvPowerSeries.coeff_mul d _ _

end GlobalTheory.SeriesNakayama
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DiscriminantEqJacobianCompleteIntersectionDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.DiscrJacGlobal
open EtBaseChange

theorem top_le_of_closedPoint {T : Type} [CommRing T] [IsLocalRing T] {X : Scheme.{0}} (w : Sp T ⟶ X) {U : X.Opens}
    (h : w (IsLocalRing.closedPoint T) ∈ U) : ⊤ ≤ w ⁻¹ᵁ U :=
  fun p _ => ((IsLocalRing.specializes_closedPoint p).map w.continuous).mem_open U.isOpen h

theorem exists_unit_chart {R T : Type} [CommRing R] [CommRing T] (x : KeyIn R) (w : Sp T ⟶ x.P.A.left)
    (c c' : x.P.L.ι) (h : ⊤ ≤ w ⁻¹ᵁ x.P.L.U c) (h' : ⊤ ≤ w ⁻¹ᵁ x.P.L.U c') :
    ∃ ω : Tˣ, ∀ (l : ℕ) (s : RR x l), valT w (x.P.L.U c) (s.f c) = (ω : T) ^ l * valT w (x.P.L.U c') (s.f c') := by
  have hp : ⊤ ≤ w ⁻¹ᵁ (x.P.L.U c ⊓ x.P.L.U c') := fun p hp => ⟨h hp, h' hp⟩
  refine ⟨Units.map (valH w _ hp).toMonoidHom (x.P.L.g c c'), fun l s => ?_⟩
  have hs : rs x.P.A.left (inf_le_left : x.P.L.U c ⊓ x.P.L.U c' ≤ x.P.L.U c) (s.f c) =
      ((x.P.L.g c c' ^ (l : ℤ) : Γ(x.P.A.left, x.P.L.U c ⊓ x.P.L.U c')ˣ) : Γ(x.P.A.left, x.P.L.U c ⊓ x.P.L.U c')) *
        rs x.P.A.left inf_le_right (s.f c') := s.compat c c'
  refine (valT_res w inf_le_left hp _).symm.trans ((congrArg (valT w _) hs).trans ?_)
  refine (valT_eq w _ hp _).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ ?_))
  · rw [zpow_natCast, Units.val_pow_eq_pow_val, map_pow]; rfl
  · exact (valT_eq w _ hp _).symm.trans (valT_res w _ hp _)

theorem notMem_nonzeroLocus {R T : Type} [CommRing R] [CommRing T] [IsLocalRing T] (x : KeyIn R)
    (w : Sp T ⟶ x.P.A.left) (c : x.P.L.ι) (h : ⊤ ≤ w ⁻¹ᵁ x.P.L.U c) {l : ℕ} (s : RR x l)
    (hs : valT w (x.P.L.U c) (s.f c) = 0) : w (IsLocalRing.closedPoint T) ∉ Out.nonzeroLocus s := by
  intro hy
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  have h₁ := top_le_of_closedPoint w hk
  have hle := x.P.A.left.basicOpen_le (s.f k)
  obtain ⟨ω, hω⟩ := exists_unit_chart x w k c (fun p hp => hle (h₁ hp)) h
  have e := valT_res w hle h₁ (s.f k)
  rw [valT_eq w _ h₁] at e
  have hu : IsUnit (valT w (x.P.L.U k) (s.f k)) :=
    e ▸ (x.P.A.left.toRingedSpace.isUnit_res_basicOpen (s.f k)).map (valH w _ h₁)
  rw [hω, hs, mul_zero] at hu
  exact not_isUnit_zero hu

theorem valT_cst {R T : Type} [CommRing R] [CommRing T] {X : Scheme.{0}} (π : X ⟶ Sp R) (f : R →+* T)
    (w : Sp T ⟶ X) (hw : w ≫ π = spMap f) (U : X.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U) (c : R) :
    valT w U (cst π U c) = f c := by
  have h0 : valT w U (cst π U c) =
      valT w U ((π.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)) := rfl
  refine h0.trans ((valT_appLE w π (U := ⊤) le_top h _).trans ?_)
  rw [hw, ← Category.comp_id (spMap f), valT_spMap f (𝟙 (Sp R)) (U := ⊤) le_top, valT_eq (𝟙 (Sp R)) ⊤ le_top]
  have e3 : Scheme.Hom.appLE (𝟙 (Sp R)) ⊤ ⊤ le_top = 𝟙 _ := by
    rw [← Scheme.Hom.id_appTop]; exact Scheme.Hom.appLE_eq_app _
  unfold valH
  erw [e3]
  simp

theorem eval_det_pderiv_mul {O : Type} [CommRing O] {g : ℕ} (e : MvPowerSeries (Fin g) O →ₐ[O] O)
    (ω : MvPowerSeries (Fin g) O) (F : Fin g → MvPowerSeries (Fin g) O) (hF : ∀ i, e (F i) = 0) :
    e (Matrix.of fun i j => MvPowerSeries.pderiv (R := O) j (ω * F i)).det =
      e ω ^ g * e (Matrix.of fun i j => MvPowerSeries.pderiv (R := O) j (F i)).det := by
  rw [AlgHom.map_det, AlgHom.map_det]
  refine Eq.trans ?_ ((Matrix.det_smul _ (e ω)).trans (by rw [Fintype.card_fin]))
  congr 1
  ext i j
  simp [hF]

theorem main : Out.Laws → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (x : KeyIn O) (n l d : ℕ) (s : Fin x.P.g → RR x n) (b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (m) (z : Fin d → Pt x) (ch : Fin d → x.P.L.ι), 1 ≤ n → x.P.g * n < l → (∀ j ≤ x.P.g, IsBasis x (b j)) → IsMul x l s b m → {y : x.P.A.left | x.P.A.hom y = IsLocalRing.closedPoint O ∧ ∀ i, y ∉ Out.nonzeroLocus (s i)}.Finite → (∀ a, ⊤ ≤ (z a).left ⁻¹ᵁ x.P.L.U (ch a)) → (∀ a i, valT (T := O) (z a).left (x.P.L.U (ch a)) ((s i).f (ch a)) = 0) → (∀ a, GlobalTheory.KeyKa.jac x s (z a) (ch a) ≠ 0) → Function.Injective z → (∀ y : x.P.A.left, x.P.A.hom y ≠ IsLocalRing.closedPoint O → (∀ i, y ∉ Out.nonzeroLocus (s i)) → ∃ a, ∃ p : Sp O, (z a).left p = y) → ∃ (ev₀ : ∀ j, Matrix (Fin d) (Fin ((l - j * n) ^ x.P.g)) O) (Pm : Matrix (Fin d) (Fin d) O) (t₀ : O), (Matrix.of fun a k => valT (T := O) (z a).left (x.P.L.U (ch a)) ((b 0 k).f (ch a))) = Pm * ev₀ 0 ∧ IsCx kdeg (kosD (N := fun j => (l - j * n) ^ x.P.g) m ev₀) ∧ TorsSq kdeg (kosD (N := fun j => (l - j * n) ^ x.P.g) m ev₀) t₀ ∧ Associated (Pm.det ^ 2) (∏ a, GlobalTheory.KeyKa.jac x s (z a) (ch a)) := by
  intro laws O _ _ _ _ x n l d s b m z ch hn hl hb hm hfin hz hs hj hinj hex
  classical
  let p₀ : Fin d → x.P.A.left := fun a => (z a).left (IsLocalRing.closedPoint O)
  let Y : Type := Set.range p₀
  let p : Fin d → Y := fun a => ⟨p₀ a, a, rfl⟩
  have hY : Finite Y := (Set.finite_range p₀).to_subtype
  choose r hr using fun y : Y => y.2
  choose θ hθ₀ hθ₁ hθ₂ hθ₃ using fun y : Y =>
    GlobalTheory.FormalChart.exists_formal_chart O x.P.A.left x.P.A.hom x.P.g (z (r y)).left x.P.smoothDim (Over.w (z (r y)))
  have hθ : ∀ y : Y, θ y (IsLocalRing.closedPoint _) = y.1 := fun y => (hθ₀ y).trans (hr y)
  choose e he₁ he₂ using fun a => hθ₃ (p a) O (z a).left
    ((Over.w (z a)).trans (Spec.map_id _).symm) (hθ (p a)).symm
  have hc : ∀ y, ⊤ ≤ θ y ⁻¹ᵁ x.P.L.U (ch (r y)) := fun y => top_le_of_closedPoint _ (by
    rw [hθ₀]; exact hz (r y) (x := IsLocalRing.closedPoint O) trivial)
  have hc' : ∀ a, ⊤ ≤ θ (p a) ⁻¹ᵁ x.P.L.U (ch a) := fun a => top_le_of_closedPoint _ (by
    rw [hθ]; exact hz a (x := IsLocalRing.closedPoint O) trivial)
  choose ω hω using fun a => exists_unit_chart x (θ (p a)) (ch a) (ch (r (p a))) (hc' a) (hc (p a))
  let F : Y → Fin x.P.g → MvPowerSeries (Fin x.P.g) O := fun y i =>
    valT (θ y) (x.P.L.U (ch (r y))) ((s i).f (ch (r y)))
  let ρ : ∀ j, Y → Fin ((l - j * n) ^ x.P.g) → MvPowerSeries (Fin x.P.g) O := fun j y k =>
    valT (θ y) (x.P.L.U (ch (r y))) ((b j k).f (ch (r y)))
  let u : Fin d → Oˣ := fun a => Units.map (e a).toMonoidHom (ω a)
  have hval : ∀ a (k : ℕ) (sg : RR x k), valT (T := O) (z a).left (x.P.L.U (ch a)) (sg.f (ch a)) =
      (u a : O) ^ k * e a (valT (θ (p a)) (x.P.L.U (ch (r (p a)))) (sg.f (ch (r (p a))))) := fun a k sg => by
    have h := valT_spMap (e a).toRingHom (θ (p a)) (hc' a) (sg.f (ch a))
    rw [he₂, hω, map_mul, map_pow] at h
    exact h
  have hF : ∀ a i, e a (F (p a) i) = 0 := fun a i =>
    ((u a).isUnit.pow n).mul_right_eq_zero.1 ((hval a n (s i)).symm.trans (hs a i))
  have hZ : FinZ x s := by
    have : Finite (Sp O) := by
      refine Set.finite_univ_iff.1 ((Set.toFinite {(⊥ : PrimeSpectrum O), IsLocalRing.closedPoint O}).subset
        fun q _ => ?_)
      by_cases hq : PrimeSpectrum.asIdeal q = ⊥
      · exact Or.inl (PrimeSpectrum.ext hq)
      · exact Or.inr (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal ((PrimeSpectrum.isPrime q).isMaximal hq)))
    refine (hfin.union (Set.finite_range fun q : Fin d × Sp O => (z q.1).left q.2)).subset fun y hy => ?_
    by_cases h : x.P.A.hom y = IsLocalRing.closedPoint O
    · exact Or.inl ⟨h, hy⟩
    · obtain ⟨a, q, hq⟩ := hex y h hy
      exact Or.inr ⟨(a, q), hq⟩
  have hcx := (KoszulCx.koszul_isCx O x n l d s b z ch hl hb).2 m hm hz hs
  have hcl := GlobalTheory.KosResidueExact.main laws O _ (IsLocalRing.residue O) x n l s b m hn hl hb hm hZ
  have hgen := GlobalTheory.KeyKa.KoszulGenExact.kosD_exact_generic laws O _ (algebraMap O (FractionRing O)) x n l s b m d z ch
    (IsFractionRing.injective O _) hn hl hb hm hz hs hj hinj (fun y ⟨q, hq⟩ => hex y fun h => by
      have h₁ := congrArg PrimeSpectrum.asIdeal (hq.trans h)
      have h₂ : q.asIdeal = ⊥ := (Ideal.eq_bot_or_top _).resolve_right q.isPrime.ne_top
      change Ideal.comap (algebraMap O (FractionRing O)) q.asIdeal = IsLocalRing.maximalIdeal O at h₁
      rw [h₂, Ideal.comap_bot_of_injective _ (IsFractionRing.injective O _)] at h₁
      exact IsDiscreteValuationRing.not_a_field O h₁.symm)
  obtain ⟨hK₁, hK₂⟩ := GlobalTheory.KeyKa.KosKer.ker_and_image O x.P.g d _ m _ hcx hgen hcl
  let K := AlgebraicClosure (IsLocalRing.ResidueField O)
  let f : O →+* K := (algebraMap (IsLocalRing.ResidueField O) K).comp (IsLocalRing.residue O)
  have hf : RingHom.ker f = IsLocalRing.maximalIdeal O := by
    rw [← RingHom.comap_ker, (RingHom.injective_iff_ker_eq_bot _).1 (algebraMap (IsLocalRing.ResidueField O) K).injective]
    exact IsLocalRing.ker_residue
  have hsurj := GlobalTheory.SeriesNakayama.span_mod_equations_lift O K f x.P.g _ Y F (ρ 0) hf (GlobalTheory.KeyKa.exists_sub_mem_of_dense K x.P.g _ Y _ _
    (GlobalTheory.KeyKa.exists_comb_sub_mem_sup_pow laws O K f x n l s b m Y θ (fun y => ch (r y)) hf hn hl hb hm hZ hθ₁ hθ₂ hc
      (fun y y' h => Subtype.ext ((hθ y).symm.trans (h.trans (hθ y'))))
      (fun y i => by
        rw [hθ₀]
        exact notMem_nonzeroLocus (T := O) x _ _ (hz (r y)) _ (hs (r y) i))))
  have hmul : ∀ y i k, F y i * ρ 1 y k = ∑ k', m i 0 1 k' k • ρ 0 y k' := fun y i k => by
    have h := congrArg (valH (θ y) _ (hc y)) (hm i 0 i.pos k (ch (r y)))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, map_sum] at h
    refine (congrArg₂ (· * ·) (valT_eq _ _ (hc y) _) (valT_eq _ _ (hc y) _)).trans
      (h.trans (Finset.sum_congr rfl fun k' _ => (map_mul _ _ _).trans ?_))
    rw [Algebra.smul_def]
    exact congrArg₂ (· * ·) ((valT_eq _ _ (hc y) _).symm.trans (valT_cst x.P.A.hom _ (θ y) (hθ₁ y) _ (hc y) _))
      (valT_eq _ _ (hc y) _).symm
  obtain ⟨E, Pm, h₁, h₂, h₃, h₄⟩ := GlobalTheory.DiscrJacobianBlocks.exists_factor_associated_jacobian O x.P.g d _ Y p F (ρ 0) e (fun a => u a ^ (l - 0 * n))
    (Matrix.of fun a k => valT (T := O) (z a).left (x.P.L.U (ch a)) ((b 0 k).f (ch a))) hF he₁
    (fun a k => hval a _ (b 0 k)) hsurj (fun v hv y => by
      obtain ⟨w, rfl⟩ := hK₁ v hv
      have : ∑ k, (∑ i, (m i 0 1).mulVec (w i)) k • ρ 0 y k = ∑ i, ∑ k', w i k' • (F y i * ρ 1 y k') := by
        simp only [hmul, Finset.sum_apply, Finset.sum_smul, Finset.smul_sum, Matrix.mulVec, dotProduct, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        simp only [_root_.mul_comm]
      rw [this]
      exact Ideal.sum_mem _ fun i _ => Ideal.sum_mem _ fun k' _ => Submodule.smul_of_tower_mem _ _
        (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩))) hK₂
  let ev₀ : ∀ j, Matrix (Fin d) (Fin ((l - j * n) ^ x.P.g)) O := fun j => Nat.casesOn j E fun _ => 0
  obtain ⟨h₅, t₀, h₆⟩ := GlobalTheory.KeyKa.KoszulTors.koszul_tors O x.P.g d _ m _ ev₀ Pm hcx h₁ h₂ h₃ hK₁ hcl
  refine ⟨ev₀, Pm, t₀, h₁, h₅, h₆, h₄.trans (Associated.prod _ _ _ fun a _ => ?_)⟩
  obtain ⟨v, hv⟩ := GlobalTheory.KeyKa.jac_eq_unit_mul_det_pderiv O x (θ (p a)) (z a) (e a) (hθ₁ _) (hθ₂ _) (hθ₃ _) (he₁ a) (he₂ a)
  rw [hv n s (ch a) (hz a)]
  simp only [hω]
  rw [eval_det_pderiv_mul (e a) _ (F (p a)) (hF a), ← _root_.mul_assoc]
  exact (associated_unit_mul_right _ _ (v.isUnit.mul ((((ω a).isUnit.pow n).map (e a)).pow _)))

end GlobalTheory.DiscrJacGlobal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DiscriminantEqJacobianCompleteIntersectionDvrStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discriminant_eq_jacobian_complete_intersection_dvr : Out.Laws → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (x : KeyIn O) (n l d : ℕ) (s : Fin x.P.g → RR x n) (b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (m) (z : Fin d → Pt x) (ch : Fin d → x.P.L.ι), 1 ≤ n → x.P.g * n < l → (∀ j ≤ x.P.g, IsBasis x (b j)) → IsMul x l s b m → {y : x.P.A.left | x.P.A.hom y = IsLocalRing.closedPoint O ∧ ∀ i, y ∉ Out.nonzeroLocus (s i)}.Finite → (∀ a, ⊤ ≤ (z a).left ⁻¹ᵁ x.P.L.U (ch a)) → (∀ a i, valT (T := O) (z a).left (x.P.L.U (ch a)) ((s i).f (ch a)) = 0) → (∀ a, GlobalTheory.KeyKa.jac x s (z a) (ch a) ≠ 0) → Function.Injective z → (∀ y : x.P.A.left, x.P.A.hom y ≠ IsLocalRing.closedPoint O → (∀ i, y ∉ Out.nonzeroLocus (s i)) → ∃ a, ∃ p : Sp O, (z a).left p = y) → ∃ (ev₀ : ∀ j, Matrix (Fin d) (Fin ((l - j * n) ^ x.P.g)) O) (Pm : Matrix (Fin d) (Fin d) O) (t₀ : O), (Matrix.of fun a k => valT (T := O) (z a).left (x.P.L.U (ch a)) ((b 0 k).f (ch a))) = Pm * ev₀ 0 ∧ IsCx kdeg (kosD (N := fun j => (l - j * n) ^ x.P.g) m ev₀) ∧ TorsSq kdeg (kosD (N := fun j => (l - j * n) ^ x.P.g) m ev₀) t₀ ∧ Associated (Pm.det ^ 2) (∏ a, GlobalTheory.KeyKa.jac x s (z a) (ch a)) := by
  first | exact @GlobalTheory.DiscrJacGlobal.main | exact GlobalTheory.DiscrJacGlobal.main | (intros; apply GlobalTheory.DiscrJacGlobal.main <;> assumption)
end
