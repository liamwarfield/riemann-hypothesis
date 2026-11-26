module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPtOfOfDecoRaw
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LamJsymRead
open Formalism.L2.Col

noncomputable section

namespace GlobalTheory.LamRead

theorem sum_skip {F : Type} [Field F] {n r k : ℕ} (hr : r ≤ n) (hk : k ≤ r) (N : Matrix (Fin n) (Fin n) F) (f : ℕ → ℕ → F)
    (hf : ∀ i j : Fin n, f i.1 j.1 = N i j) :
    (∑ x : Fin n, ∑ y : Fin n, if (x : ℕ) + 1 = y ∧ (y : ℕ) < r ∧ (y : ℕ) ≠ k then N x y else 0) =
      ∑ i ∈ Finset.range (k - 1), f i (i + 1) + ∑ i ∈ Finset.range (r - k - 1), f (k + i) (k + i + 1) := by
  rw [Formalism.L2.G.sum_sup hr k ((Finset.range r).filter (fun x => x + 1 ≠ k))
    (fun x hx => by simp only [Finset.mem_filter, Finset.mem_range]; constructor <;> intro h <;> first | exact h.2 | exact ⟨by omega, h⟩) N,
    Finset.filter_filter, Finset.sum_filter]
  have h1 : ∀ x ∈ Finset.range r, (if x + 1 ≠ k ∧ x + 1 < r then Formalism.L2.G.entN N x (x + 1) else 0) =
      if x + 1 < r ∧ x + 1 ≠ k then f x (x + 1) else 0 := fun x hx => by
    by_cases hx' : x + 1 < r ∧ x + 1 ≠ k
    · rw [if_pos hx', if_pos ⟨hx'.2, hx'.1⟩]
      have a1 : x < n := by omega
      have a2 : x + 1 < n := by omega
      unfold Formalism.L2.G.entN
      rw [dif_pos ⟨a1, a2⟩]
      exact (hf ⟨x, a1⟩ ⟨x + 1, a2⟩).symm
    · rw [if_neg hx', if_neg (fun h => hx' ⟨h.2, h.1⟩)]
  rw [Finset.sum_congr rfl h1]
  obtain ⟨d, rfl⟩ : ∃ d, r = k + d := ⟨r - k, by omega⟩
  rw [Finset.sum_range_add, Nat.add_sub_cancel_left]
  by_cases hd : d = 0
  · subst hd
    rw [GlobalTheory.TopLawSym.sum_pred k _ _ fun p hp => by omega]
    simp
  · rw [GlobalTheory.TopLawSym.sum_pred k _ _ fun p hp => by omega,
      GlobalTheory.TopLawSym.sum_pred d (fun p => f (k + p) (k + p + 1)) (fun p => k + p + 1 < k + d ∧ k + p + 1 ≠ k) fun p hp => by omega]

theorem coarse_iff {r m t s i : ℕ} (ht : 0 < t) (hs : s < m) :
    coarse r (List.replicate m t) i = s + 1 ↔ r + s * t ≤ i ∧ i < r + s * t + t := by
  have hb := GlobalTheory.DatumLaw.blk_le (r := r) (a := r + m * t) hs le_rfl
  by_cases hir : i < r
  · rw [coarse_of_lt hir]
    omega
  · by_cases h2 : i < r + m * t
    · rw [GlobalTheory.TopLawSym.coarse_eq ht (by omega) h2, Nat.add_right_cancel_iff, Nat.div_eq_iff ht]
      omega
    · rw [coarse_of_le (by omega), blkIdx_replicate_of_le t m _ (by
        have := Nat.sub_le_sub_right (Nat.not_lt.1 h2) r
        rwa [Nat.add_sub_cancel_left] at this)]
      omega

theorem lamJsym_read (κ κ' K : Type) [CommRing κ] [Field κ'] [Field K] (e : κ →+* κ') (emb : K →+* ℂ) (ψ : AddChar κ K)
    (χ : ℕ → κˣ →* Kˣ) (ψ' : AddChar κ' ℂ) (χ' : ℕ → MulChar κ' ℂ) (n k r t m rS : ℕ) (h : r ≤ n) (hr : r = k + 2 * rS + 1)
    (ht : 0 < t) (hn : r + m * t ≤ n) (hψ : ∀ x, ψ' (e x) = emb (ψ x))
    (hχ : ∀ s, s < m → ∀ c : κˣ, χ' s (e c) = emb ((χ s c : Kˣ) : K)) (M : HJsym κ n k r t m rS h) :
    emb ((lamJsym ψ χ n k r t m rS h M : Kˣ) : K) =
      Formalism.L2.Forms.lamSym ψ' χ' k rS t m ((M.1 : Matrix (Fin n) (Fin n) κ).map e) := by
  let A : ℕ → ℕ → κ := fun i j => if h' : i < n ∧ j < n then (M.1 : Matrix (Fin n) (Fin n) κ) ⟨i, h'.1⟩ ⟨j, h'.2⟩ else 0
  have hA : ∀ i j : Fin n, A i.1 j.1 = (M.1 : Matrix (Fin n) (Fin n) κ) i j := fun i j => dif_pos ⟨i.2, j.2⟩
  have h0 : ((lamJsym ψ χ n k r t m rS h M : Kˣ) : K) =
      ((chiSymF ψ r k rS (HPar0 h _ _ M) : Kˣ) : K) *
        ((detChar χ n r (List.replicate m t) ⟨M.1, HPar_le h _ _ M.2⟩ : Kˣ) : K) := rfl
  have hrS : Formalism.L2.Forms.rSym k rS = r := hr.symm
  rw [h0, GlobalTheory.TopLawSym.chiSymF_val ψ (by omega) (HPar0 h _ _ M) A fun i j => hA (Fin.castLE h i) (Fin.castLE h j), detChar_apply,
    List.length_replicate, Units.coe_prod, map_mul, map_prod, ← hψ]
  unfold Formalism.L2.Forms.lamSym Formalism.L2.Forms.lamJ
  rw [hrS]
  congr 1
  · congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [sum_skip h (by omega) _ (fun i j => e (A i j)) fun i j => by rw [hA]; rfl, map_add (f := _), map_sum, map_sum]
  · refine Finset.prod_congr rfl fun s hs => ?_
    rw [Finset.mem_range] at hs
    rw [← hχ s hs, GlobalTheory.TopLaw.blkDet_eq_dB (coarse r (List.replicate m t)) (s + 1) (r + s * t) t (GlobalTheory.DatumLaw.blk_le hs hn)
      (fun i _ => coarse_iff ht hs) ⟨M.1, HPar_le h _ _ M.2⟩ A hA]
    unfold GlobalTheory.DatumLaw.dB
    rw [RingHom.map_det]
    congr 2
    ext u v
    have hb := GlobalTheory.DatumLaw.blk_le hs hn
    have a1 : r + s * t + u.1 < n := by have := u.2; omega
    have a2 : r + s * t + v.1 < n := by have := v.2; omega
    show e (A (r + s * t + u.1) (r + s * t + v.1)) = Formalism.L2.Forms.entN _ (r + s * t + u.1) (r + s * t + v.1)
    unfold Formalism.L2.Forms.entN
    rw [dif_pos ⟨a1, a2⟩]
    exact congrArg e (hA ⟨_, a1⟩ ⟨_, a2⟩)

end GlobalTheory.LamRead
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoarseLast
open Formalism.L2.Col

namespace GlobalTheory.MemXSym

open Formalism.L2.Forms

theorem facts {n k r t m rS : ℕ} (hr : r = k + 2 * rS + 1) (ht : 0 < t) (hn : n = r + m * t + 1) (x : ℕ) (hx : x < n) :
    (x < r ∧ coarse r (List.replicate m t) x = 0 ∧ lvSym k rS t x = symIdx k rS x ∧ symIdx k rS x < r) ∨
    (r ≤ x ∧ lvSym k rS t x + 1 = r + coarse r (List.replicate m t) x ∧ 1 ≤ coarse r (List.replicate m t) x) := by
  rcases Nat.lt_or_ge x r with h1 | h1
  · refine Or.inl ⟨h1, coarse_of_lt h1, ?_, ?_⟩
    · have : x < rSym k rS := by unfold rSym; omega
      rw [lvSym_of_lt this]; unfold posSym symIdx; split_ifs <;> omega
    · unfold symIdx; split_ifs <;> omega
  · refine Or.inr ⟨h1, ?_, by rw [coarse_of_le h1]; omega⟩
    have hx' : ¬ x < rSym k rS := by unfold rSym; omega
    have hs : rSym k rS = r := by unfold rSym; omega
    unfold lvSym; rw [if_neg hx', hs]
    rcases Nat.lt_or_ge x (r + m * t) with h2 | h2
    · rw [GlobalTheory.TopLawSym.coarse_eq ht h1 h2, Nat.add_assoc]
    · have hx2 : x = r + m * t := by omega
      subst hx2
      rw [coarse_of_le h1, blkIdx_replicate_of_le t m (r + m * t - r) (by omega), Nat.add_sub_cancel_left,
        Nat.mul_div_cancel _ ht, Nat.add_assoc]

theorem facts_lt {k r t rS x : ℕ} (hr : r = k + 2 * rS + 1) (hx : x < r) :
    lvSym k rS t x = symIdx k rS x := by
  have : x < rSym k rS := by unfold rSym; omega
  rw [lvSym_of_lt this]; unfold posSym symIdx; split_ifs <;> omega

theorem coarse_last {r t m x : ℕ} (hx : x < r + m * t) :
    coarse r (List.replicate m t) x < coarse r (List.replicate m t) (r + m * t) := by
  have cN : coarse r (List.replicate m t) (r + m * t) = m + 1 := by
    rw [coarse_of_le (by omega), blkIdx_replicate_of_le t m (r + m * t - r) (by omega)]
  rw [cN]
  rcases Nat.lt_or_ge x r with h1 | h1
  · rw [coarse_of_lt h1]; omega
  · rw [coarse_of_le h1]; have := blkIdx_replicate_lt t m (x - r) (by omega); omega

variable {κ : Type} [Field κ]

theorem inJ_of_mem {n k r t m rS : ℕ} (h : r ≤ n) (hr : r = k + 2 * rS + 1) (ht : 0 < t) (hn : n = r + m * t + 1)
    {M : GL (Fin n) κ} (hM : M ∈ HXmsym κ n k r t m rS h) : InJSym k rS t true (M : Matrix (Fin n) (Fin n) κ) := by
  obtain ⟨hJ, hF⟩ := Subgroup.mem_inf.mp hM
  have hF' : ∀ i j : Fin n, j.val = r + m * t → (M : Matrix (Fin n) (Fin n) κ) i j = (1 : Matrix (Fin n) (Fin n) κ) i j := hF
  obtain ⟨hB, h0⟩ := mem_HPar.mp hJ
  have hkr : k + rS ≤ r := by omega
  rw [mem_HPsymF_iff hkr] at h0
  obtain ⟨p1, p2, p3⟩ := h0
  refine ⟨fun x y hxy => ?_, fun x hx => ?_, fun x y hx hy => ?_, fun _ x y hy => ?_⟩
  · rcases facts hr ht hn x.val x.2 with ⟨hx, cx, lx, sx⟩ | ⟨hx, lx, cx⟩ <;>
      rcases facts hr ht hn y.val y.2 with ⟨hy, cy, ly, sy⟩ | ⟨hy, ly, cy⟩
    · rw [lx, ly] at hxy
      exact p1 ⟨x, hx⟩ ⟨y, hy⟩ hxy
    · exfalso; omega
    · exact (mem_btG.mp hB) x y (by omega)
    · exact (mem_btG.mp hB) x y (by omega)
  · exact p2 ⟨x, by unfold rSym at hx; omega⟩
  · exact p3 ⟨x, by omega⟩ ⟨y, by omega⟩ hx hy
  · have hy' : y.val = r + m * t := by omega
    constructor
    · rw [hF' x y hy', Matrix.one_apply]
    · by_cases hxy : x = y
      · subst hxy; rw [hF' x x hy', Matrix.one_apply]
      · rw [if_neg hxy]
        apply (mem_btG.mp hB) y x
        have hx1 : x.val < r + m * t := by
          have := x.2; have : x.val ≠ y.val := fun e => hxy (Fin.ext e); omega
        rw [hy']
        exact coarse_last hx1

theorem mem_of_inJ {n k r t m rS : ℕ} (h : r ≤ n) (hr : r = k + 2 * rS + 1) (ht : 0 < t) (hn : n = r + m * t + 1)
    {M : GL (Fin n) κ} (hM : InJSym k rS t true (M : Matrix (Fin n) (Fin n) κ)) : M ∈ HXmsym κ n k r t m rS h := by
  obtain ⟨q1, q2, q3, q4⟩ := hM
  have hkr : k + rS ≤ r := by omega
  have hB : M ∈ blockUT n κ r (List.replicate m t) := mem_btG.mpr fun x y hxy => q1 x y (by
    rcases facts hr ht hn x.val x.2 with ⟨hx, cx, lx, sx⟩ | ⟨hx, lx, cx⟩ <;>
      rcases facts hr ht hn y.val y.2 with ⟨hy, cy, ly, sy⟩ | ⟨hy, ly, cy⟩ <;> omega)
  refine Subgroup.mem_inf.mpr ⟨mem_HPar.mpr ⟨hB, ?_⟩, ?_⟩
  · rw [mem_HPsymF_iff hkr]
    refine ⟨fun i j hij => ?_, fun i => ?_, fun i j hi hj => ?_⟩
    · refine q1 (Fin.castLE h i) (Fin.castLE h j) ?_
      simp only [Fin.coe_castLE]
      rw [facts_lt hr i.2, facts_lt hr j.2]
      exact hij
    · exact q2 (Fin.castLE h i) (by simp only [Fin.coe_castLE]; unfold rSym; omega)
    · exact q3 (Fin.castLE h i) (Fin.castLE h j) (by simpa using hi) (by simpa using hj)
  · intro x y hy
    rw [(q4 rfl x y (by omega)).1, Matrix.one_apply]

theorem memX (κ : Type) [Field κ] (n k r t m rS : ℕ) (h : r ≤ n) (hr : r = k + 2 * rS + 1) (ht : 0 < t)
    (hn : n = r + m * t + 1) (M : GL (Fin n) κ) :
    M ∈ HXmsym κ n k r t m rS h ↔ M ∈ Formalism.L2.Forms.JSymG κ n k rS t true := by
  constructor
  · intro hM
    show InJSym k rS t true _ ∧ InJSym k rS t true _
    exact ⟨inJ_of_mem h hr ht hn hM, inJ_of_mem h hr ht hn (Subgroup.inv_mem _ hM)⟩
  · intro hM
    exact mem_of_inJ h hr ht hn hM.1

end GlobalTheory.MemXSym
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TypeLev

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

def badB (B : Base) : Set (HeightOneSpectrum (𝓞 B.host.F)) :=
  {v | (B.host.g 0 : 𝓞 B.host.F) ∈ v.asIdeal ∨ (B.host.g 1 : 𝓞 B.host.F) ∈ v.asIdeal}

theorem mem_badB {v : HeightOneSpectrum (𝓞 B.host.F)} : v ∈ badB B ↔ ∃ j, (B.host.g j : 𝓞 B.host.F) ∈ v.asIdeal := by
  rw [Fin.exists_fin_two]; rfl

theorem not_mem_both {A : Type} [CommRing A] {P : Ideal A} (hP : P.IsPrime) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : p ≠ q)
    (a : (p : A) ∈ P) (b : (q : A) ∈ P) : False := by
  obtain ⟨x, y, e⟩ := (Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 h)).map (Int.castRingHom A)
  refine hP.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  rw [← e]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (by simpa using a)) (Ideal.mul_mem_left _ _ (by simpa using b))

theorem T_notMem (hPr : (B.primes X).Ok) (u : B.Word) {v : HeightOneSpectrum (𝓞 B.host.F)} (hv : v ∈ badB B) :
    (B.T u : 𝓞 B.host.F) ∉ v.asIdeal := fun h => by
  obtain ⟨j, hj⟩ := mem_badB.1 hv
  exact not_mem_both v.isPrime (hPr.T_prime u) (hPr.g_prime j) (hPr.T_ne_g u j) h hj

theorem piT_dvd (hPr : (B.primes X).Ok) (u : B.Word) :
    X.piT u ∣ algebraMap (𝓞 B.host.F) (𝓞 B.host.E) (B.T u : 𝓞 B.host.F) := by
  rw [map_natCast]
  exact ⟨_, (hPr.piT_norm u).symm⟩

theorem under_notMem (hPr : (B.primes X).Ok) (u : B.Word) {P : HeightOneSpectrum (𝓞 B.host.E)} (h : X.piT u ∈ P.asIdeal) :
    underPl B.host.F P ∉ badB B := fun hv =>
  T_notMem hPr u hv (Ideal.mem_comap.2 (Ideal.mem_of_dvd _ (piT_dvd hPr u) h))

local instance isEmpty_Q : IsEmpty (I.Q I.mu0) := by rw [I.twistPrimes_reference_tuple_eq_empty]; infer_instance

local instance neZero_top (R : Ranks) : NeZero (R.N R.m) := ⟨by have := N_m_succ R; omega⟩

local instance neZero_rankPred (R : Ranks) : NeZero (R.N R.m - 1) := ⟨by have := rank_X'_eq R; have := rSym_rSD R; unfold rSym at this; omega⟩


set_option maxHeartbeats 1000000 in
theorem rdM (hPr : (B.primes X).Ok) (u : B.Word) {Lb U chi y st k}
    (h : I.Reads u I.mu0 B.R.m (fun _ => ()) (fun _ => Lb) (fun _ => U) (fun _ => chi) y st k) (c : (I.stp u I.mu0 B.R.m).Cl) :
    RdLev (E := B.fields.E) B.sp.cm U chi (badB B) (levGTop I.Ch I.Ps) B.embLL := by
  have hd : Disjoint (B.primes X).vGs (I.Q I.mu0) := by rw [I.twistPrimes_reference_tuple_eq_empty]; exact Finset.disjoint_empty_right _
  have h0 : ∀ q : (I.stp u I.mu0 B.R.m).D c.1, cosetIn q = fun _ => ∅ := fun q => by
    have h1 := q.2
    rw [ysAt_ys_of_ne I.sel (I.tup I.mu0) (I.cst I.mu0) (by omega)] at h1
    funext P
    unfold cosetIn
    rw [Set.mem_singleton_iff.1 h1]
    simp
  have := rdLev_of_reads (X := B.fields) (hc := B.sp.cm) (bad := badB B)
    (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) B.R.m c.1) (levQAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) B.R.m c.1)
    B.embLL (U := U) (chi := chi) (IsPtOf.of_extTo (I.Q_subset_SQ _) hd (h.pt c))
    (fun v hv => h.k_off () v (T_notMem hPr u hv) (fun ⟨P, hP, _⟩ => isEmptyElim (⟨P, hP⟩ : I.Q I.mu0)) (Or.inl rfl))
    (fun P hP => under_notMem hPr u ((mem_divs (fun e => (hPr.T_prime u).ne_zero (by
      have := hPr.piT_norm u
      rw [show (B.primes X).piT u = 0 from e, zero_mul] at this
      exact Nat.cast_eq_zero.1 this.symm)) P).1 hP))
    (fun x q hq => (h.lev c x q hq).trans (exists_congr fun κ => and_congr_right fun _ => and_iff_left ((h0 _).trans (h0 _).symm)))
    (fun x κ h1 h2 => h.chr c x κ h1 h2)
  rwa [levGAt_of_le _ _ _ _ le_rfl, topLev_levG_m] at this


set_option maxHeartbeats 1000000 in
theorem rdP {Lb U chi y lat st} (h : I.ReadsP I.mu0 Lb U chi y lat st) (c : (I.stX I.mu0).Cl) :
    RdLev (E := B.fields.E) B.sp.cm U chi (badB B) (rowTyG I.Ch I.Ps) B.embLL :=
  rdLev_of_reads (X := B.fields) (hc := B.sp.cm) (bad := badB B) (rowTyG I.Ch I.Ps) (levQX B.R I.sel (I.tup I.mu0))
    B.embLL (U := U) (chi := chi) (y := y c) (k := 1) (p := ((I.stX I.mu0).rep c).1.1) (by rw [mul_one]; exact h.pt c)
    (fun v _ => map_one _) (fun P hP => absurd hP (Finset.notMem_empty _))
    (fun x q hq => h.lev c x q (by rwa [mul_one] at hq))
    (fun x κ h1 h2 => h.chr c x κ h1 (by rwa [mul_one] at h2))

theorem cmp_base (hPr : (B.primes X).Ok) (G : GLoc B.host.F B.host.E B.sp.cm.sig B.host.g) (hG : G.piG = X.piG) :
    Nonempty (Cmp G (B.primes X).vGs) := by
  classical
  have h0 : ∀ i, B.fields.conjO ((B.primes X).piG i) ≠ 0 := fun i h => by
    have := hPr.piG_norm i
    rw [h, mul_zero] at this
    exact (hPr.g_prime i).ne_zero (Nat.cast_eq_zero.1 this.symm)
  have hm : ∀ w, w ∈ (B.primes X).vGs ↔ ∃ i, B.fields.conjO ((B.primes X).piG i) ∈ w.asIdeal := fun w => by
    unfold Primes.vGs Primes.vG
    simp only [Finset.mem_union, mem_divs (h0 _), Fin.exists_fin_two]
  refine nonempty_cmp B.host B.sp.cm (levOk_base B X) G hPr.g_ne (fun w hw => ?_) fun j w hw => (hm w).2 ⟨j, ?_⟩
  · obtain ⟨i, hi⟩ := (hm w).1 hw
    exact ⟨i, (hPr.piG_norm i) ▸ Ideal.mul_mem_left _ _ hi⟩
  · rw [hG] at hw
    exact hw

theorem exists_nat (hPr : (B.primes X).Ok) (w : (B.primes X).vGs) (c : 𝓞 B.fields.E ⧸ w.1.asIdeal) : ∃ n : ℕ, c = n := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, w.1 ∈ (B.primes X).vG i := by
    rw [Fin.exists_fin_two]
    exact Finset.mem_union.1 w.2
  have hc : Nat.card (𝓞 B.fields.E ⧸ w.1.asIdeal) = (B.primes X).g i := by
    rw [← hPr.vG_norm i _ hi, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have := Fact.mk (hPr.g_prime i)
  have : Nontrivial (𝓞 B.fields.E ⧸ w.1.asIdeal) := Ideal.Quotient.nontrivial_iff.2 w.1.isPrime.ne_top
  have : Finite (𝓞 B.fields.E ⧸ w.1.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.1.ne_bot
  have h := zmultiples_eq_top_of_prime_card hc (one_ne_zero (α := 𝓞 B.fields.E ⧸ w.1.asIdeal))
  obtain ⟨n, hn⟩ := mem_multiples_iff_mem_zmultiples.2 (h ▸ AddSubgroup.mem_top c : c ∈ AddSubgroup.zmultiples (1 : 𝓞 B.fields.E ⧸ w.1.asIdeal))
  exact ⟨n, by simpa using hn.symm⟩


set_option maxHeartbeats 1000000 in
theorem main_base (hPr : (B.primes X).Ok) (u : B.Word) (G : GLoc B.host.F B.host.E B.sp.cm.sig B.host.g) (hG : G.piG = X.piG)
    (hψ : ∀ j v h (w : {w // w ∈ (B.primes X).vGs}), w.1.under (𝓞 B.host.F) = v → ∀ n : ℕ,
      G.psi0 j v h (n : kv B.host.F v) = B.embLL (I.Ch.psi0 w (n : 𝓞 B.fields.E ⧸ w.1.asIdeal)))
    (hχ : ∀ j v h (w : {w // w ∈ (B.primes X).vGs}), w.1.under (𝓞 B.host.F) = v → ∀ (s : Fin B.R.m) (n : ℕ)
      (c : (𝓞 B.fields.E ⧸ w.1.asIdeal)ˣ), (c : 𝓞 B.fields.E ⧸ w.1.asIdeal) = n →
      G.chiB j v h s.1 (n : kv B.host.F v) = B.embLL ((I.Ch.chi s w c : B.LLˣ) : B.LL))
    {J J' T T' f f'} (hJ : J = 1) (hJ' : J' = 1) (S : StepLevel B.host.F B.host.E B.sp.cm.sig (n := B.R.N B.R.m) J T f (badB B))
    (S' : StepLevel B.host.F B.host.E B.sp.cm.sig (n := B.R.N B.R.m - 1) J' T' f' (badB B))
    (hL : ∀ x, x ∈ S.Lb ↔ x ∈ baseL B _ (X.piT u)) (hL' : ∀ x, x ∈ S'.Lb ↔ x ∈ baseL B _ 1)
    (hR : RdLev (E := B.fields.E) B.sp.cm S.U S.chi (badB B) (levGTop I.Ch I.Ps) B.embLL)
    (hR' : RdLev (E := B.fields.E) B.sp.cm S'.U S'.chi (badB B) (rowTyG I.Ch I.Ps) B.embLL) :
    ∃ lamM lamP, ∃ (VM : GLevH S G (fun _ v _ => JSymG (kv B.host.F v) _ B.R.k (rSD B.R) B.R.t true) lamM)
      (VP : GLevH S' G (fun _ v _ => JSymG (kv B.host.F v) _ B.R.k (rSD B.R) B.R.t false) lamP),
      (∀ j v h M, ((lamM j v h M : ℂˣ) : ℂ) = lamSym (G.psi0 j v h) (G.chiB j v h) B.R.k (rSD B.R) B.R.t B.R.m M.1.1) ∧
      (∀ j v h M, ((lamP j v h M : ℂˣ) : ℂ) = lamSym (G.psi0 j v h) (G.chiB j v h) B.R.k (rSD B.R) B.R.t B.R.m M.1.1) ∧
      (∀ j v h, VP.fr j v h = 1) ∧ ∀ j v h, (VM.fr j v h).1 = diagonal fun i => if i.1 + 1 = B.R.N B.R.m then
        G.phi j v h (inclE (F := B.host.F) (v.adicCompletion B.host.F) (X.piT u : B.host.E)) else 1 := by
  obtain ⟨C⟩ := cmp_base hPr G hG
  have hr : B.R.r = B.R.k + 2 * B.R.rS + 1 := (rSym_rSD B.R).symm
  have ht : 0 < B.R.t := B.R.t_odd.pos
  have hn := rank_X'_eq B.R
  have hN := N_m_succ B.R
  have e1 : ∀ j v h x, G.psi0 j v h ((C.e j v h).toRingHom x) = B.embLL (I.Ch.psi0 (C.W j v h) x) := fun j v h x => by
    obtain ⟨n, rfl⟩ := exists_nat hPr _ x
    rw [map_natCast]
    exact hψ j v h _ (C.ov j v h) n
  have e2 : ∀ j v h s, s < B.R.m → ∀ c : (𝓞 B.fields.E ⧸ (C.W j v h).1.asIdeal)ˣ, G.chiB j v h s ((C.e j v h).toRingHom c) =
      B.embLL ((chiAt I.Ch (C.W j v h) s c : B.LLˣ) : B.LL) := fun j v h s hs c => by
    obtain ⟨n, hn⟩ := exists_nat hPr _ c.1
    rw [hn, map_natCast, show chiAt I.Ch (C.W j v h) s = I.Ch.chi ⟨s, hs⟩ (C.W j v h) from dif_pos hs]
    exact hχ j v h _ (C.ov j v h) ⟨s, hs⟩ n c hn
  have hM := fun j v h => by
    letI := (C.W j v h).1.isMaximal
    letI := Ideal.Quotient.field (C.W j v h).1.asIdeal
    exact exists_lam (k := B.R.k) (rS := rSD B.R) (t := B.R.t) (zl := true) (C.e j v h) B.embLL (levGTop I.Ch I.Ps (C.W j v h))
      (lamSym (G.psi0 j v h) (G.chiB j v h) B.R.k (rSD B.R) B.R.t B.R.m)
      (by rw [levGTop_PsymF]; exact GlobalTheory.MemXSym.memX _ _ _ _ _ _ _ _ hr ht (by omega))
      (by
        rw [levGTop_PsymF]
        exact fun M => GlobalTheory.LamRead.lamJsym_read _ _ _ (C.e j v h).toRingHom B.embLL _ _ _ _ _ _ _ _ _ _ _ hr ht (by omega)
          (e1 j v h) (e2 j v h) ⟨M.1, M.2.1⟩)
  have hP := fun j v h => by
    letI := (C.W j v h).1.isMaximal
    letI := Ideal.Quotient.field (C.W j v h).1.asIdeal
    exact exists_lam (k := B.R.k) (rS := rSD B.R) (t := B.R.t) (zl := false) (C.e j v h) B.embLL (rowTyG I.Ch I.Ps (C.W j v h))
      (lamSym (G.psi0 j v h) (G.chiB j v h) B.R.k (rSD B.R) B.R.t B.R.m)
      (GlobalTheory.mem_HJsym_iff_JSymG _ _ _ _ _ _ _ _ hr ht hn)
      (fun M => GlobalTheory.LamRead.lamJsym_read _ _ _ (C.e j v h).toRingHom B.embLL _ _ _ _ _ _ _ _ _ _ _ hr ht hn.ge
          (e1 j v h) (e2 j v h) M)
  choose lamM m1 m2 m3 using hM
  choose lamP p1 p2 p3 using hP
  have hu : ∀ j v h, IsUnit (C.ρ j v h (oToS B.host.F B.host.E (X.piT u))) := fun j v h => by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, C.e_eq, resS_oToS, map_ne_zero_iff _ (C.e j v h).injective, Ne,
      Ideal.Quotient.eq_zero_iff_mem]
    intro h'
    refine under_notMem hPr u h' ?_
    rw [C.ov]
    exact mem_badB.2 ⟨j, h⟩
  obtain ⟨VM, hVM⟩ := exists_gLevH hJ S C (fun _ => mem_badB)
    (fun v hv => locL_eq v hL (T_notMem hPr u hv) (piT_dvd hPr u)) hR _ lamM (fun j v h => lastDiag _ (hu j v h).unit) m2 m3
    fun j v h M hM => lastDiag_commute _ _ hM
  obtain ⟨VP, hVP⟩ := exists_gLevH hJ' S' C (fun _ => mem_badB)
    (fun v hv => locL_eq v hL' (T_notMem hPr u hv) (one_dvd _)) hR' _ lamP (fun j v h => 1) p2 p3
    fun j v h M hM => by rw [map_one]; exact Commute.one_left _
  refine ⟨lamM, lamP, VM, VP, m1, p1, fun j v h => by rw [hVP, map_one], fun j v h => ?_⟩
  rw [hVM]
  refine (Matrix.diagonal_map (map_zero _)).trans (congrArg diagonal (funext fun i => ?_))
  split_ifs
  · refine (C.ρ_eq j v h _).trans (congrArg _ ?_)
    exact Formalism.UG.P.afsplit_prV_inclE v _
  · exact map_one _

theorem frExt_of {D : D7} (hiX : ∀ x j, iXc D x j = if h : j.1 < D.R.N D.R.m - 1 then x ⟨j.1, h⟩ else 0) (p : D.host.E)
    (G : GLoc D.host.F D.host.E (sigD D) D.host.g) {frm frp} (h3 : ∀ j v h, frp j v h = 1)
    (h4 : ∀ j v h, Units.val (frm j v h) = diagonal fun i : Fin (D.R.N D.R.m) => if i.1 + 1 = D.R.N D.R.m then
      G.phi j v h (inclE (F := D.host.F) (v.adicCompletion D.host.F) p) else 1) :
    FrExtFr (D := D) (fun j => if j.1 + 1 = D.R.N D.R.m then p else 0) G frm frp := by
  refine fun j v h => ⟨fun x b b' hb => ?_, fun x t ht => ?_⟩
  · have hb2 := b.2
    rw [h3, h4, Units.val_one, Matrix.mul_one, Matrix.map_apply, iXm, LinearMap.toMatrix'_apply, hiX, diagonal_apply]
    by_cases hx : x = b'
    · subst hx
      rw [if_pos rfl, if_neg (by omega), dif_pos (hb ▸ hb2), Pi.single_apply, if_pos (Fin.ext hb.symm), map_one]
    · rw [if_neg hx]
      split_ifs with h5
      · rw [Pi.single_apply, if_neg (fun e : (⟨x.1, h5⟩ : Fin _) = b => hx (Fin.ext ((congrArg Fin.val e).trans hb))), map_zero]
      · rw [map_zero]
  · rw [h4, diagonal_apply]
    beta_reduce
    by_cases hx : x = t
    · subst hx
      rw [if_pos rfl, if_pos ht, if_pos ht]
    · rw [if_neg hx, if_neg fun e => hx (Fin.ext (by omega)), map_zero, map_zero]

end GlobalTheory.Mem.Col2.TypeLev

end


set_option maxHeartbeats 2000000 in
theorem GlobalTheory.Mem.Col2.TC.levels_top_row_sym : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (G : GLoc (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (I.rec7 l Z).host.g) (K : ClsTied (D := (I.rec7 l Z)) u B.R.m le_rfl) (KP : ClsPTied (D := (I.rec7 l Z)) u), I.IdG l Z G → (∃ k, I.Reads u I.mu0 B.R.m (fun _ => ()) (fun _ => K.lev.Lb) (fun _ => K.lev.U) (fun _ => K.lev.chi) (fun c => (K.y c).1) (fun c s => (K.stabI c s).1) k) → I.ReadsP I.mu0 KP.lev.Lb KP.lev.U KP.lev.chi (fun c => (KP.y c).1) KP.lat (fun c s => (KP.stabI c s).1) → ∃ (lamM : ∀ (j : Fin 2) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal → HSym (I.rec7 l Z) (B.R.N B.R.m) true v →* ℂˣ) (lamP : ∀ (j : Fin 2) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal → HSym (I.rec7 l Z) (B.R.N B.R.m - 1) false v →* ℂˣ) (VM : GLevH K.lev G (fun _ v _ => HSym (I.rec7 l Z) (B.R.N B.R.m) true v) lamM) (VP : GLevH KP.lev G (fun _ v _ => HSym (I.rec7 l Z) (B.R.N B.R.m - 1) false v) lamP), (∀ j v h M, ((lamM j v h M : ℂˣ) : ℂ) = lamSym (G.psi0 j v h) (G.chiB j v h) B.R.k (rSD B.R) B.R.t B.R.m M.1.1) ∧ (∀ j v h M, ((lamP j v h M : ℂˣ) : ℂ) = lamSym (G.psi0 j v h) (G.chiB j v h) B.R.k (rSD B.R) B.R.t B.R.m M.1.1) ∧ (∀ j v h, VP.fr j v h = 1) ∧ FrExtFr (D := (I.rec7 l Z)) (fun j => if j.1 + 1 = B.R.N B.R.m then ((X.piT u : 𝓞 B.host.E) : B.host.E) else 0) G VM.fr VP.fr := by
  intro B X I hI hP l Z u G K KP hG ⟨k, hK⟩ hKP
  obtain ⟨-, gP, hiX, hN⟩ := GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z
  obtain ⟨c, -⟩ := K.y_bij.2 (Quotient.mk'' 1)
  obtain ⟨c', -⟩ := KP.y_bij.2 (Quotient.mk'' 1)
  obtain ⟨lamM, lamP, VM, VP, h1, h2, h3, h4⟩ := TypeLev.main_base I l.pr u G hG.piG hG.psi hG.chi (hN _ le_rfl).1 gP K.lev KP.lev
    (hK.lb ()) hKP.lb (TypeLev.rdM I l.pr u hK c) (TypeLev.rdP I hKP c')
  exact ⟨lamM, lamP, VM, VP, h1, h2, h3, TypeLev.frExt_of (D := I.rec7 l Z) hiX _ G h3 h4⟩
