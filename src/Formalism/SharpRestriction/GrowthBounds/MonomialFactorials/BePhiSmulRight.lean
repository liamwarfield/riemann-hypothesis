module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestRankLProved
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BlockValuationZpOfLatticeInclusion

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.MfacMapDomainAdd
section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.PhisBRenameMul
section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestPlusAOf
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset

section Level

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

def RestPlusAW (j : Fin G.T.t → ℕ) (jp : ℕ) (D : ℤ) : Prop :=
  Formalism.GM.M.goodCount p (fun F F' => Formalism.GM.M.fockN p (G.lettersAt j jp) (G.T.phis p (r := r) (G.lettersAt j jp) F) F')
            (Formalism.GM.M.YZ p (r := r) (G.lettersAt j jp) G.T.J G.T.thr) D * dXi r (G.B - jp) ≤
    Formalism.GM.M.goodCount p (bePhi p (r := r) G j jp) (Ljj p (r := r) G j jp) D

theorem plusA_of (j : Fin G.T.t → ℕ) (jp : ℕ) (D : ℤ) (h : RestPlusAW p (r := r) G j jp D) :
    Formalism.GM.M.bad p (bePhi p (r := r) G j jp) (Ljj p (r := r) G j jp) D ≤ badY p (r := r) G j jp D * dXi r (G.B - jp) := by
  have h1 := finrank_Ljj_le p (r := r) G j jp
  have hY : Module.finrank ℤ_[p] (Formalism.GM.M.YZ p (r := r) (G.lettersAt j jp) G.T.J G.T.thr) = dimY p (r := r) G j jp :=
    Formalism.CountingSumsFrames.finrank_lattice _ _ inf_le_left
  unfold badY
  simp only [Formalism.GM.M.bad]
  rw [hY, Nat.sub_mul]
  unfold RestPlusAW at h
  omega

end Level

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

def RestPlusAWI (CM : ℝ) : Prop :=
  ∀ dl ∈ CountingStatementReduction.clSet C0 CE1 CE2 X, ∀ aTop ∈ cbox C0 CE1 CE2 X dl, ∀ x ∈ idx C0 CE1 CE2 X dl aTop,
    RestPlusAW X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 ⌊D1r C0 CE1 CE2 X CM⌋

theorem restPlusA_of (CM : ℝ) (h : RestPlusAWI C0 CE1 CE2 X CM) : RestPlusA C0 CE1 CE2 X CM := by
  intro dl hdl aTop ha x hx
  exact plusA_of X.p (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 _ (h dl hdl aTop ha x hx)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial

section Free

variable {k σ : Type} [Field k] {r : ℕ}

theorem tieE_mul_free (w e : Fin r → σ) (F m : MvPolynomial σ k) :
    Formalism.GM.tieE w e (F * m) = Formalism.GM.tieE w e F * m := by
  simp only [Formalism.GM.tieE, LinearMap.mulLeft_apply, mul_assoc]

theorem tieF_mul_free (w e : Fin r → σ) (F m : MvPolynomial σ k) (hw : ∀ c, pderiv (w c) m = 0)
    (he : ∀ c, pderiv (e c) m = 0) : Formalism.GM.tieF w e (F * m) = Formalism.GM.tieF w e F * m := by
  have key : ∀ (v : σ) (G : MvPolynomial σ k), pderiv v m = 0 → pderiv v (G * m) = pderiv v G * m := by
    intro v G hv
    rw [Derivation.leibniz, hv, smul_zero, zero_add, smul_eq_mul, mul_comm]
  unfold Formalism.GM.tieF
  rw [LinearMap.sum_apply, LinearMap.sum_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  show pderiv (w c) (pderiv (e c) (F * m)) = pderiv (w c) (pderiv (e c) F) * m
  rw [key _ _ (he c), key _ _ (hw c)]

theorem tiePhi_mul_free (w e : Fin r → σ) (o n z : ℕ) (F m : MvPolynomial σ k) (hw : ∀ c, pderiv (w c) m = 0)
    (he : ∀ c, pderiv (e c) m = 0) : Formalism.GM.tiePhi w e o n z (F * m) = Formalism.GM.tiePhi w e o n z F * m := by
  have hE : ∀ (j : ℕ) (G : MvPolynomial σ k),
      ((Formalism.GM.tieE w e) ^ j) (G * m) = ((Formalism.GM.tieE w e) ^ j) G * m := by
    intro j
    induction j with
    | zero => intro G; rfl
    | succ j ih =>
      intro G
      rw [pow_succ']
      show Formalism.GM.tieE w e (((Formalism.GM.tieE w e) ^ j) (G * m)) =
        Formalism.GM.tieE w e (((Formalism.GM.tieE w e) ^ j) G) * m
      rw [ih, tieE_mul_free]
  have hF : ∀ (j : ℕ) (G : MvPolynomial σ k),
      ((Formalism.GM.tieF w e) ^ j) (G * m) = ((Formalism.GM.tieF w e) ^ j) G * m := by
    intro j
    induction j with
    | zero => intro G; rfl
    | succ j ih =>
      intro G
      rw [pow_succ']
      show Formalism.GM.tieF w e (((Formalism.GM.tieF w e) ^ j) (G * m)) =
        Formalism.GM.tieF w e (((Formalism.GM.tieF w e) ^ j) G) * m
      rw [ih, tieF_mul_free w e _ m hw he]
  unfold Formalism.GM.tiePhi
  rw [LinearMap.sum_apply, LinearMap.sum_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.comp_apply, hF, hE,
    smul_mul_assoc]

theorem foldr_mul_free {ι : Type*} (l : List ι) (f : ι → MvPolynomial σ k →ₗ[k] MvPolynomial σ k) (m : MvPolynomial σ k)
    (h : ∀ i ∈ l, ∀ F, f i (F * m) = f i F * m) (F : MvPolynomial σ k) :
    (l.foldr (fun i acc => f i ∘ₗ acc) LinearMap.id) (F * m) = (l.foldr (fun i acc => f i ∘ₗ acc) LinearMap.id) F * m := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldr_cons, LinearMap.comp_apply]
    rw [ih (fun j hj => h j (List.mem_cons_of_mem _ hj)), h i (by simp)]

theorem foldr_rename {τ : Type} {ι : Type*} (l : List ι) (em : σ → τ)
    (f : ι → MvPolynomial σ k →ₗ[k] MvPolynomial σ k) (g : ι → MvPolynomial τ k →ₗ[k] MvPolynomial τ k)
    (h : ∀ i ∈ l, ∀ F, g i (rename em F) = rename em (f i F)) (F : MvPolynomial σ k) :
    (l.foldr (fun i acc => g i ∘ₗ acc) LinearMap.id) (rename em F) =
      rename em ((l.foldr (fun i acc => f i ∘ₗ acc) LinearMap.id) F) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldr_cons, LinearMap.comp_apply]
    rw [ih (fun j hj => h j (List.mem_cons_of_mem _ hj)), h i (by simp)]

end Free

section Level

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

theorem phisB_rename_mul (hB : G.BlockOK) (j : Fin G.T.t → ℕ) (jp : ℕ) (y : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (m : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p])
    (hm : ∀ (a : Fin N) (c : Fin r), pderiv (Sum.inl (Fin.castSucc a, c)) m = 0) :
    phisB p (r := r) G j jp (rename (Formalism.GM.M.chainEmb N r G.T.t) y * m) =
      rename (Formalism.GM.M.chainEmb N r G.T.t) (G.T.phis p (r := r) (G.lettersAt j jp) y) * m := by
  obtain ⟨-, hpos, -, hN⟩ := hB
  have hlt : ∀ i : Fin G.T.t, G.T.pos i + 1 < N := fun i => by have := hpos i; omega
  have hfin0 : ∀ i : Fin G.T.t, Formalism.GM.M.finPos N (G.T.pos i) =
      Fin.castSucc (⟨G.T.pos i, by have := hlt i; omega⟩ : Fin N) := by
    intro i
    apply Fin.ext
    simp only [Formalism.GM.M.finPos, Fin.coe_castSucc]
    have := hlt i
    omega
  have hfin1 : ∀ i : Fin G.T.t, Formalism.GM.M.finPos N (G.T.pos i + 1) =
      Fin.castSucc (⟨G.T.pos i + 1, hlt i⟩ : Fin N) := by
    intro i
    apply Fin.ext
    simp only [Formalism.GM.M.finPos, Fin.coe_castSucc]
    have := hlt i
    omega
  have hlet0 : ∀ i : Fin G.T.t, G.letterAt (G.T.pos i) = (⟨G.T.pos i, by have := hlt i; omega⟩ : Fin N) := by
    intro i
    apply Fin.ext
    simp only [Formalism.GM.M.BlockData.letterAt]
    have := hlt i
    omega
  have hlet1 : ∀ i : Fin G.T.t, G.letterAt (G.T.pos i + 1) = (⟨G.T.pos i + 1, hlt i⟩ : Fin N) := by
    intro i
    apply Fin.ext
    simp only [Formalism.GM.M.BlockData.letterAt]
    have := hlt i
    omega
  have hinj : Function.Injective (Formalism.GM.M.chainEmb N r G.T.t) := by
    intro x y h
    simp only [Formalism.GM.M.chainEmb, Sum.inl.injEq, Prod.mk.injEq, Fin.castSucc_inj] at h
    exact Prod.ext h.1 h.2
  unfold phisB
  rw [foldr_mul_free]
  · congr 1
    unfold Formalism.GM.M.TieData.phis
    refine foldr_rename _ _ _ _ (fun i _ F => ?_) y
    simp only [Formalism.GM.M.TieData.phi, dif_pos (hlt i), Formalism.GM.M.tiePhiAt]
    rw [hfin0, hfin1, hlet0, hlet1]
    exact Formalism.CountingSumsFrames.TO.tiePhi_rename (Formalism.GM.M.chainEmb N r G.T.t) hinj
      (fun c : Fin r => ((⟨G.T.pos i, by have := hlt i; omega⟩ : Fin N), c))
      (fun c : Fin r => ((⟨G.T.pos i + 1, hlt i⟩ : Fin N), c)) _ _ _ F
  · intro i _ F
    exact tiePhi_mul_free _ _ _ _ _ F m (fun c => by rw [hfin0]; exact hm _ c)
      (fun c => by rw [hfin1]; exact hm _ c)

end Level

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.GM.ProjS

section Disj

variable {k σ τ : Type} [Field k] [DecidableEq σ] [DecidableEq τ]

theorem mapDomain_add_inj (e : τ → σ) (he : Function.Injective e) (a b : τ →₀ ℕ) (β β' : σ →₀ ℕ)
    (hβ : ∀ x, β (e x) = 0) (hβ' : ∀ x, β' (e x) = 0)
    (h : Finsupp.mapDomain e a + β = Finsupp.mapDomain e b + β') : a = b ∧ β = β' := by
  have ha : a = b := by
    ext x
    have h1 := DFunLike.congr_fun h (e x)
    simpa [Finsupp.mapDomain_apply_of_injective he, hβ, hβ'] using h1
  subst ha
  exact ⟨rfl, add_left_cancel h⟩

theorem mfac_mapDomain_add (e : τ → σ) (he : Function.Injective e) (a : τ →₀ ℕ) (β : σ →₀ ℕ)
    (hβ : ∀ x, β (e x) = 0) : (mfac (Finsupp.mapDomain e a + β) : k) = mfac a * mfac β := by
  unfold mfac
  have hd : Disjoint (Finsupp.mapDomain e a).support β.support := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hx)
    exact (Finsupp.mem_support_iff.1 hx') (hβ y)
  rw [Finsupp.prod_add_index_of_disjoint hd, Finsupp.prod_mapDomain_index_inj he]

theorem fockK_rename_mul (e : τ → σ) (he : Function.Injective e) (A B : MvPolynomial τ k) (β β' : σ →₀ ℕ) (c : k)
    (hβ : ∀ x, β (e x) = 0) (hβ' : ∀ x, β' (e x) = 0) :
    Formalism.GM.M.fockK (rename e A * monomial β 1) (rename e B * monomial β' c) =
      if β = β' then c * mfac β * Formalism.GM.M.fockK A B else 0 := by
  classical
  set F := rename e A * monomial β (1 : k) with hF
  set G := rename e B * monomial β' c with hG
  have hcF : ∀ m, F.coeff (Finsupp.mapDomain e m + β) = A.coeff m := by
    intro m
    rw [hF, MvPolynomial.coeff_mul_monomial, MvPolynomial.coeff_rename_mapDomain e he, mul_one]
  have hcF0 : ∀ n, F.coeff n ≠ 0 → ∃ m, n = Finsupp.mapDomain e m + β ∧ A.coeff m ≠ 0 := by
    intro n hn
    rw [hF, MvPolynomial.coeff_mul_monomial'] at hn
    split_ifs at hn with hle
    · rw [mul_one] at hn
      obtain ⟨u, hu, hu0⟩ := MvPolynomial.coeff_rename_ne_zero e A (n - β) hn
      refine ⟨u, ?_, hu0⟩
      rw [hu]
      exact (tsub_add_cancel_of_le hle).symm
    · exact absurd rfl hn
  have hcG : ∀ m, G.coeff (Finsupp.mapDomain e m + β) = if β = β' then B.coeff m * c else 0 := by
    intro m
    split_ifs with hb
    · subst hb
      rw [hG, MvPolynomial.coeff_mul_monomial, MvPolynomial.coeff_rename_mapDomain e he]
    · by_contra hne
      rw [hG, MvPolynomial.coeff_mul_monomial'] at hne
      split_ifs at hne with hle
      · have h1 : (rename e B).coeff (Finsupp.mapDomain e m + β - β') ≠ 0 := fun h0 => hne (by rw [h0, zero_mul])
        obtain ⟨u, hu, -⟩ := MvPolynomial.coeff_rename_ne_zero e B _ h1
        have h2 : Finsupp.mapDomain e m + β = Finsupp.mapDomain e u + β' := by
          rw [hu]
          exact (tsub_add_cancel_of_le hle).symm
        exact hb (mapDomain_add_inj e he m u β β' hβ hβ' h2).2
      · exact hne rfl
  have hmf : ∀ m : τ →₀ ℕ, ((Finsupp.mapDomain e m + β).prod fun _ j => (j.factorial : k)) =
      (m.prod fun _ j => (j.factorial : k)) * (β.prod fun _ j => (j.factorial : k)) :=
    fun m => mfac_mapDomain_add e he m β hβ
  unfold Formalism.GM.M.fockK
  have hsub : F.support ⊆ A.support.image (fun m => Finsupp.mapDomain e m + β) := by
    intro n hn
    obtain ⟨m, rfl, hm⟩ := hcF0 n (MvPolynomial.mem_support_iff.1 hn)
    exact Finset.mem_image.2 ⟨m, MvPolynomial.mem_support_iff.2 hm, rfl⟩
  rw [Finset.sum_subset hsub (fun n _ hn => by
    rw [MvPolynomial.mem_support_iff, not_not] at hn
    rw [hn]
    ring)]
  have hinj : Set.InjOn (fun m => Finsupp.mapDomain e m + β) A.support :=
    fun a _ b _ hab => (mapDomain_add_inj e he a b β β hβ hβ hab).1
  rw [Finset.sum_image hinj]
  simp only [hcF, hcG, hmf]
  split_ifs with hb
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    unfold mfac
    ring
  · simp

end Disj

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.GM.ProjS

section Level

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

theorem exists_fd_Ljj (j : Fin G.T.t → ℕ) (jp : ℕ) :
    ∃ W : Submodule ℚ_[p] (MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]), FiniteDimensional ℚ_[p] W ∧
      ∀ x ∈ Ljj p (r := r) G j jp, x ∈ W := by
  classical
  set Yq := Formalism.GM.M.Y p (r := r) (G.lettersAt j jp) G.T.J G.T.thr with hYq
  have : FiniteDimensional ℚ_[p] (Formalism.GM.M.Pol p r (G.lettersAt j jp)) := Formalism.CountingSumsFrames.pol_finiteDimensional _
  have : FiniteDimensional ℚ_[p] Yq := Submodule.finiteDimensional_of_le inf_le_left
  let bY := Module.finBasis ℚ_[p] Yq
  let Ms := xiMons (r := r) G (G.B - jp)
  let fam : Fin (Module.finrank ℚ_[p] Yq) × Ms → MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p] :=
    fun ab => rename (Formalism.GM.M.chainEmb N r G.T.t) ((bY ab.1 : Yq) : _) * monomial (ab.2 : _ →₀ ℕ) 1
  let W := Submodule.span ℚ_[p] (Set.range fam)
  have hsub : ∀ x ∈ Ljj p (r := r) G j jp, x ∈ W := by
    intro x hx
    have hle : Ljj p (r := r) G j jp ≤ W.restrictScalars ℤ_[p] := by
      unfold Ljj
      rw [Submodule.span_le]
      rintro _ ⟨y, hy, g, hg, rfl⟩
      have hyY : y ∈ Yq := (Submodule.mem_inf.1 hy).1
      have hy2 : y ∈ Submodule.span ℚ_[p] (Set.range fun a => ((bY a : Yq) : MvPolynomial _ ℚ_[p])) := by
        have h3 : (⟨y, hyY⟩ : Yq) ∈ (⊤ : Submodule ℚ_[p] Yq) := Submodule.mem_top
        rw [← bY.span_eq] at h3
        have h4 := Submodule.mem_map_of_mem (f := Yq.subtype) h3
        rw [Submodule.map_span, ← Set.range_comp] at h4
        exact h4
      have hg2 := xi_mem_span p G (G.B - jp) g hg
      show rename (Formalism.GM.M.chainEmb N r G.T.t) y * g ∈ W
      have hy3 : rename (Formalism.GM.M.chainEmb N r G.T.t) y ∈ Submodule.span ℚ_[p]
          (Set.range fun a => rename (Formalism.GM.M.chainEmb N r G.T.t) ((bY a : Yq) : MvPolynomial _ ℚ_[p])) := by
        have := Submodule.mem_map_of_mem (f := (rename (Formalism.GM.M.chainEmb N r G.T.t) :
          MvPolynomial _ ℚ_[p] →ₐ[ℚ_[p]] MvPolynomial _ ℚ_[p]).toLinearMap) hy2
        rw [Submodule.map_span, ← Set.range_comp] at this
        exact this
      have hmul := Submodule.mul_mem_mul hy3 hg2
      rw [Submodule.span_mul_span] at hmul
      refine Submodule.span_mono ?_ hmul
      rintro _ ⟨u, ⟨a, rfl⟩, v, ⟨m, hm, rfl⟩, rfl⟩
      exact ⟨(a, ⟨m, hm⟩), rfl⟩
    exact hle hx
  exact ⟨W, FiniteDimensional.span_of_finite ℚ_[p] (Set.finite_range fam), hsub⟩

theorem bePhi_smul_left (j : Fin G.T.t → ℕ) (jp : ℕ) (c : ℚ_[p]) (u v : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]) :
    bePhi p (r := r) G j jp (c • u) v = c * bePhi p (r := r) G j jp u v := by
  unfold bePhi
  rw [map_smul, fockK_smul_left, mul_div_assoc]

theorem bePhi_sum_left (j : Fin G.T.t → ℕ) (jp : ℕ) {ι : Type} (s : Finset ι) (f : ι → MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p])
    (v : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]) :
    bePhi p (r := r) G j jp (∑ i ∈ s, f i) v = ∑ i ∈ s, bePhi p (r := r) G j jp (f i) v := by
  unfold bePhi
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, fockK_sum_left, Finset.sum_div]

theorem bePhi_smul_right (j : Fin G.T.t → ℕ) (jp : ℕ) (c : ℚ_[p]) (u v : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]) :
    bePhi p (r := r) G j jp u (c • v) = c * bePhi p (r := r) G j jp u v := by
  unfold bePhi
  rw [fockK_smul_right, mul_div_assoc]

theorem gcL_bdd (j : Fin G.T.t → ℕ) (jp : ℕ) (D : ℤ) :
    BddAbove {n | ∃ x y : Fin n → MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p],
      (∀ i, x i ∈ Ljj p (r := r) G j jp) ∧ (∀ i, y i ∈ Ljj p (r := r) G j jp) ∧
      ∀ i k, bePhi p (r := r) G j jp (x i) (y k) = if i = k then (p : ℚ_[p]) ^ D else 0} := by
  classical
  obtain ⟨W, hW, hsub⟩ := exists_fd_Ljj p (r := r) G j jp
  refine ⟨Module.finrank ℚ_[p] W, ?_⟩
  rintro n ⟨x, y, hx, hy, hxy⟩
  have hp0 : (p : ℚ_[p]) ^ D ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have hli : LinearIndependent ℚ_[p] (fun i => (⟨x i, hsub _ (hx i)⟩ : W)) := by
    rw [linearIndependent_iff']
    intro s g hs i hi
    have h0 : ∑ k ∈ s, g k • x k = 0 := by
      have := congrArg Subtype.val hs
      simpa using this
    have h1 := congrArg (fun u => bePhi p (r := r) G j jp u (y i)) h0
    simp only [bePhi_sum_left, bePhi_smul_left, hxy] at h1
    rw [Finset.sum_eq_single i (fun k _ hk => by rw [if_neg hk, mul_zero]) (fun h => absurd hi h), if_pos rfl] at h1
    have h2 : bePhi p (r := r) G j jp 0 (y i) = 0 := by
      have := bePhi_smul_left p (r := r) G j jp 0 0 (y i)
      simpa using this
    rw [h2] at h1
    exact (mul_eq_zero.1 h1).resolve_right hp0
  have := hli.fintype_card_le_finrank
  simpa using this

theorem xiMons_spec (n : ℕ) (m : Formalism.GM.M.BVar N r G.T.t →₀ ℕ) (hm : m ∈ xiMons (r := r) G n) :
    (∀ v ∈ m.support, ∃ c, v = Formalism.GM.M.xiVar N r G.T.t c) ∧ (∑ c, m (Formalism.GM.M.xiVar N r G.T.t c) = n) ∧
      (∑ v ∈ m.support, m v = n) := by
  classical
  unfold xiMons at hm
  rw [Finset.mem_image] at hm
  obtain ⟨e, he, rfl⟩ := hm
  have hsum := (CountingStatementReduction.mem_Ev e).1 he
  have happ : ∀ c, (∑ d : Fin r, Finsupp.single (Formalism.GM.M.xiVar N r G.T.t d) (e d)) (Formalism.GM.M.xiVar N r G.T.t c) = e c := by
    intro c
    rw [Finsupp.finsetSum_apply, Finset.sum_eq_single c]
    · simp
    · intro d _ hd
      rw [Finsupp.single_apply, if_neg]
      intro h
      exact hd (xiVar_inj (r := r) G h)
    · intro h; exact absurd (Finset.mem_univ c) h
  refine ⟨fun v hv => ?_, by simp only [happ]; exact hsum, ?_⟩
  · by_contra hne
    push Not at hne
    apply Finsupp.mem_support_iff.1 hv
    rw [Finsupp.finsetSum_apply]
    refine Finset.sum_eq_zero fun d _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hne d h.symm
  · have : (∑ d : Fin r, Finsupp.single (Formalism.GM.M.xiVar N r G.T.t d) (e d)).sum (fun _ k => k) = ∑ c, e c := by
      rw [← Finsupp.sum_finsetSum_index (fun _ => rfl) (fun _ _ _ => rfl)]
      exact Finset.sum_congr rfl fun d _ => Finsupp.sum_single_index rfl
    rw [← hsum, ← this]
    rfl

theorem card_xiMons_eq (n : ℕ) : (xiMons (r := r) G n).card = dXi r n := by
  classical
  unfold xiMons
  rw [Finset.card_image_of_injective]
  · rw [CountingStatementReduction.card_Ev]
    unfold dXi
    have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.2 (NeZero.ne r)
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    have e1 : r' + 1 + n - 1 = n + r' := by omega
    have e2 : n + (r' + 1) - 1 = n + r' := by omega
    rw [e1, e2, Nat.add_sub_cancel, Nat.choose_symm_add]
  · intro e e' h
    funext c
    have := congrArg (fun f : Formalism.GM.M.BVar N r G.T.t →₀ ℕ => f (Formalism.GM.M.xiVar N r G.T.t c)) h
    simp only [Finsupp.finsetSum_apply] at this
    rwa [Finset.sum_eq_single c (fun d _ hd => by rw [Finsupp.single_apply, if_neg (fun h => hd (xiVar_inj (r := r) G h))])
      (fun h => absurd (Finset.mem_univ c) h), Finset.sum_eq_single c
      (fun d _ hd => by rw [Finsupp.single_apply, if_neg (fun h => hd (xiVar_inj (r := r) G h))])
      (fun h => absurd (Finset.mem_univ c) h), Finsupp.single_eq_same, Finsupp.single_eq_same] at this

end Level

end Formalism.MainNotions.G.SymmetricFormBlocks

end
