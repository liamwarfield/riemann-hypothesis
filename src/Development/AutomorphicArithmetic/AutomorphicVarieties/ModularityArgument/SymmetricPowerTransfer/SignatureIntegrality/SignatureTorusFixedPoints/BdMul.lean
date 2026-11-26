module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.FactJ

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.BdMul
noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem UpperTheory.V.Z.Sym.Sig.kc_le (V : Lev k) : Kc k n (V.c + 1) ≤ V.J n := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨u, hu, t, l, hl, ht, hl', rfl⟩ := GlAx.udl _ (Ideal.pow_le_self (Nat.succ_ne_zero _)) y hy
  rw [map_mul, map_mul]
  refine mul_mem (mul_mem (V.N_le ⟨?_, u, rfl⟩) (V.TH_le (V.Tc_le_TH ⟨?_, _, ht, rfl⟩))) (V.Nm_le ⟨?_, l, hl', rfl⟩)
  · have h := (mem_unipB _).1 hu
    exact (mem_unipB _).2 ⟨fun i j hij => congrArg Subtype.val (h.1 i j hij), fun i => congrArg Subtype.val (h.2 i)⟩
  · refine ⟨fun i => Units.map (algebraMap 𝒪[k] k).toMonoidHom (t i),
      fun i => (Valuation.integer.integers (valuation k)).one_of_isUnit (t i).isUnit, ?_⟩
    ext i j
    show _ = algebraMap 𝒪[k] k ((diagT _ _ t : Matrix _ _ _) i j)
    rw [val_diagT, val_diagT, diagonal_apply, diagonal_apply]
    split_ifs
    · rfl
    · simp
  · have h := GlAx.mem_low.1 hl
    exact GlAx.mem_low.2 ⟨fun i j hij => congrArg Subtype.val (h.1 i j hij), fun i => congrArg Subtype.val (h.2 i)⟩

private theorem bd_mul {c : ℤ} {a : GL (Fin n) k} (ha : a ∈ KO k (Fin n)) (M : Matrix (Fin n) (Fin n) k)
    (hM : ∀ i j, valuation k (M i j) ≤ uniformizer k ^ c) (i j : Fin n) : valuation k ((a.val * M) i j) ≤ uniformizer k ^ c := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun r _ => ?_
  rw [map_mul]
  exact (mul_le_mul' (GlAx.bd_zero.1 (GlAx.mem_KO.1 ha).1 i r) (hM r j)).trans_eq (one_mul _)

end

theorem UpperTheory.V.Z.Sym.Sig.memJ : UpperTheory.V.Z.Sym.Sig.MemJ := by
  intro k _ _ _ _ V n g
  rw [GlAx.unif_spec, ← zpow_natCast]
  constructor
  · intro hg
    refine ⟨GlAx.bd_zero.1 (GlAx.mem_KO.1 (V.J_le_KO hg)).1, ?_⟩
    obtain ⟨a, ha, _, ⟨s, hs, rfl⟩, b, hb, rfl⟩ := (factJ k V n).1 g hg
    have h0 : a * diagT k (Fin n) s ∈ KO k (Fin n) := mul_mem ha.2 (V.J_le_KO (V.dg_mem fun i => hs i trivial))
    have h1 := bd_mul h0 _ (GlAx.mem_Kc.1 hb.2).1
    have h2 := (mem_unipB _).1 ha.1
    have e : ∀ i j, ((a * diagT k (Fin n) s).val * (b.val - 1)) i j = (a * diagT k (Fin n) s * b).val i j - a.val i j * s j := fun i j => by
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_apply, ← Units.val_mul, Units.val_mul a, val_diagT, mul_diagonal]
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · have := h1 i j
      rwa [e, h2.1 i j hij, zero_mul, sub_zero] at this
    · have h3 := h1 i i
      rw [e, h2.2, one_mul] at h3
      have h4 : valuation k (s i : k) = 1 := V.H_le (hs i trivial)
      generalize (a * diagT k (Fin n) s * b).val i i = x at h3
      have h5 : valuation k (x / s i - 1) ≤ uniformizer k ^ ((V.c + 1 : ℕ) : ℤ) := by
        rw [div_sub_one (s i).ne_zero, map_div₀, h4, div_one]; exact h3
      have h6 : valuation k (x / s i) = 1 := by
        have := Valuation.map_one_add_of_lt _ (h5.trans_lt (zpow_lt_one₀ GlAx.unif_pos uniformizer_lt_one (by omega)))
        rwa [add_sub_cancel] at this
      exact ⟨Units.mk0 (x / s i) (fun h => by simp [h] at h6) * s i, mul_mem (V.le (mem_Uc.2 ⟨h6, h5⟩)) (hs i trivial), by simp⟩
  · rintro ⟨h1, h2, h3⟩
    choose s hs es using h3
    have h4 : ∀ i, valuation k (s i : k) = 1 := fun i => V.H_le (hs i)
    let U : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => if i < j then ⟨g.val i j / s j, by
      show valuation k _ ≤ 1
      rw [map_div₀, h4, div_one]; exact h1 i j⟩ else if i = j then 1 else 0
    have hU : U.det = 1 := by
      rw [Matrix.det_of_upperTriangular (fun i j h => by
        have h' : j < i := h
        simp [U, h'.ne', h'.le.not_gt])]
      simp [U]
    let u := GeneralLinearGroup.map (algebraMap 𝒪[k] k) (GeneralLinearGroup.mk'' U (by rw [hU]; exact isUnit_one))
    have eu : ∀ i j, u.val i j = if i < j then g.val i j / s j else if i = j then 1 else 0 := fun i j => by
      show ((U i j : 𝒪[k]) : k) = _
      simp only [U]
      split_ifs <;> rfl
    have hu : u ∈ (glIwa k n).N := ⟨(mem_unipB _).2 ⟨fun i j h => by simp [eu, h.ne', h.le.not_gt], fun i => by simp [eu]⟩, _, rfl⟩
    have h5 : u * dg s ∈ V.J n := mul_mem (V.N_le hu) (V.dg_mem hs)
    have h6 : ∀ i j, valuation k ((g.val - (u * dg s).val) i j) ≤ uniformizer k ^ ((V.c + 1 : ℕ) : ℤ) := fun i j => by
      rw [Matrix.sub_apply, Units.val_mul, dg, val_diagT, mul_diagonal, eu]
      rcases lt_trichotomy i j with h | rfl | h
      · simp [h]
      · simp [es]
      · simpa [h.ne', h.le.not_gt] using h2 i j h
    have h7 : GlAx.Bd ((V.c + 1 : ℕ) : ℤ) ((u * dg s)⁻¹ * g) := fun i j => by
      have := bd_mul (V.J_le_KO (inv_mem h5)) _ h6 i j
      rwa [Matrix.mul_sub, ← Units.val_mul, ← Units.val_mul, inv_mul_cancel] at this
    have h8 : (u * dg s)⁻¹ * g ∈ KO k (Fin n) := by
      generalize (u * dg s)⁻¹ * g = x at h7
      have h9 := GlAx.bd_zero.1 (h7.mono (by omega))
      let X : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨x.val i j, h9 i j⟩
      have hX : X.map (IsLocalRing.residue 𝒪[k]) = 1 := by
        ext i j
        have : X i j - (1 : Matrix (Fin n) (Fin n) 𝒪[k]) i j ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
          rw [← pow_one (IsLocalRing.maximalIdeal 𝒪[k]), GlAx.mem_pow]
          have := h7.mono (show ((1 : ℕ) : ℤ) ≤ _ by omega) i j
          convert this using 2
          simp only [Matrix.sub_apply, Matrix.one_apply]
          split_ifs <;> rfl
        rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero] at this
        rw [map_apply, this]
        simp only [Matrix.one_apply]
        split_ifs <;> simp
      have hd : IsUnit X.det := by
        rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, RingHom.mapMatrix_apply, hX, det_one]
        exact one_ne_zero
      exact ⟨GeneralLinearGroup.mk'' X hd, Units.ext rfl⟩
    have := mul_mem h5 (kc_le V (mem_Kc_of h8 h7))
    rwa [mul_inv_cancel_left] at this

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Contract
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Shrink
noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

private theorem vo {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : kˣ) :
    valuation k (x : k) = uniformizer k ^ ord k x := by
  have h1 := GlAx.val_div_ord x
  have h2 := GlAx.val_zpow (k := k) (ord k x)
  have e : (x : k) = ((x / unif k ^ ord k x : kˣ) : k) * ((unif k ^ ord k x : kˣ) : k) := by
    rw [← Units.val_mul, div_mul_cancel]
  rw [e, map_mul, h1, h2, one_mul]

theorem UpperTheory.V.Z.Sym.Sig.shrink : UpperTheory.V.Z.Sym.Sig.Shrink := by
  intro k _ _ _ _ n d hd m
  set a : Fin n → ℤ := fun i => ord k (d i) with ha
  have hv : ∀ i, valuation k (d i : k) = uniformizer k ^ a i := fun i => vo (d i)
  have hlt : ∀ i j : Fin n, i < j → a j < a i := by
    intro i j hij
    have h := hd i j hij
    rw [hv, hv] at h
    exact (zpow_right_strictAnti₀ GlAx.unif_pos ValuativeRel.uniformizer_lt_one).lt_iff_gt.1 h
  have hanti : Antitone a := by
    intro i j hij
    rcases hij.lt_or_eq with h | h
    · exact (hlt i j h).le
    · rw [h]
  have hv' : ∀ i, valuation k ((d⁻¹) i : k) = uniformizer k ^ (-a i) := by
    intro i
    rw [Pi.inv_apply, Units.val_inv_eq_inv_val, map_inv₀, hv, _root_.zpow_neg]
  refine ⟨fun x hx hxm => ?_, fun c y hy hym => ?_⟩
  · have hx' : x ∈ unipB k (Fin n) ⊓ KO k (Fin n) := hx
    refine Subgroup.mem_inf.2 ⟨GlAx.conj_N hv hanti hx, ?_⟩
    rw [GlAx.mem_Kc] at hxm ⊢
    refine GlAx.conj_Kc (c' := ((m + 1 : ℕ) : ℤ)) (Subgroup.mem_inf.1 hx').1 hxm d a hv ?_
    intro i j
    rcases le_or_gt j i with h | h
    · exact Or.inl fun z hz => GlAx.up_sub_one hz h
    · right
      have := hlt i j h
      push_cast
      omega
  · have hy' : y ∈ Subgroup.comap (GlobalTheory.CuspRep.invT n k) (unipB k (Fin n)) ⊓ Kc k n (c + 1) := hy
    have e1 : (dg d)⁻¹ = diagT k (Fin n) d⁻¹ := (map_inv _ _).symm
    have e2 : dg d = (diagT k (Fin n) d⁻¹)⁻¹ := by
      rw [← map_inv, inv_inv]
    rw [e1, e2]
    refine Subgroup.mem_inf.2 ⟨GlAx.conj_Nm (a := fun i => -a i) hv' (c := c) (c' := c) ?_ hy, ?_⟩
    · intro i j h
      have := hlt j i h
      omega
    · rw [GlAx.mem_Kc] at hym ⊢
      refine GlAx.conj_Kc (c' := ((m + 1 : ℕ) : ℤ)) (Subgroup.mem_inf.1 hy').1 hym d⁻¹
        (fun i => -a i) hv' ?_
      intro i j
      rcases le_or_gt i j with h | h
      · exact Or.inl fun z hz => GlAx.low_sub_one hz h
      · right
        have := hlt j i h
        push_cast
        omega

end
end

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

private theorem quot0 {R : Type} [CommRing R] (I : Ideal R) (u v : R ⧸ I ^ 0) : u = v := by
  haveI : Subsingleton (R ⧸ I ^ 0) := Ideal.Quotient.subsingleton_iff.mpr (by simp)
  exact Subsingleton.elim u v

private theorem mem_kc_zero_of_mem_ko {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} (x : GL (Fin n) k) (hx : x ∈ KO k (Fin n)) :
    x ∈ Kc k n 0 := by
  obtain ⟨x0, rfl⟩ := hx
  refine ⟨x0, MonoidHom.mem_ker.2 ?_, rfl⟩
  exact Units.ext (Matrix.ext fun i j => quot0 _ _ _)

private theorem conj_mem_kc_of_mem_ko {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} (m : ℕ) (t x : GL (Fin n) k) (ht : t ∈ KO k (Fin n))
    (hx : x ∈ Kc k n m) : t * x * t⁻¹ ∈ Kc k n m := by
  obtain ⟨t0, rfl⟩ := ht
  obtain ⟨x0, hx0, rfl⟩ := hx
  exact ⟨t0 * x0 * t0⁻¹, (MonoidHom.normal_ker _).conj_mem x0 hx0 t0, by simp [map_mul, map_inv]⟩

private theorem mem_ko_and_torus_of_mem_th {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} (V : Lev k) (t : GL (Fin n) k) (ht : t ∈ V.TH n) :
    t ∈ KO k (Fin n) ∧ t ∈ (glIwa k n).T := by
  obtain ⟨d, hd, rfl⟩ := ht
  have hv : ∀ i, valuation k (d i : k) = 1 := fun i => V.H_le (hd i (Set.mem_univ i))
  refine ⟨?_, ⟨d, fun i => hv i, rfl⟩⟩
  have hO : ∀ i, (d i : k) ∈ 𝒪[k] := fun i => (Valuation.mem_integer_iff _ _).2 (hv i).le
  let d0 : Fin n → (𝒪[k])ˣ := fun i =>
    ((Valuation.integer.integers (valuation k)).isUnit_of_one' (x := ⟨d i, hO i⟩) (hv i)).unit
  refine ⟨diagT (𝒪[k]) (Fin n) d0, ?_⟩
  ext i j
  simp [diagT, leviEmb, leviTorus, Matrix.diagonal_apply]
  split_ifs <;> simp [d0] <;> rfl

private theorem map_mem_j_of_pres {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} (V : Lev k) (σ : GL (Fin n) k →* GL (Fin n) k)
    (hσ : Pres V σ) (g : GL (Fin n) k) (hg : g ∈ V.J n) : σ g ∈ V.J n := by
  unfold Lev.J at hg ⊢
  have h : (glIwa k n).N ⊔ V.TH n ⊔ (glIwa k n).Nm V.c ≤
      ((glIwa k n).N ⊔ V.TH n ⊔ (glIwa k n).Nm V.c).comap σ := by
    refine sup_le (sup_le ?_ ?_) ?_ <;> intro x hx <;> rw [Subgroup.mem_comap]
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (hσ.N x hx))
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (hσ.T x hx))
    · exact Subgroup.mem_sup_right (hσ.Nm V.c x hx)
  exact h hg

theorem UpperTheory.V.Z.Sym.Sig.contract : UpperTheory.V.Z.Sym.Sig.Contract := by
  intro k _ _ _ _ V n σ hσ d hd g hg
  obtain ⟨x, hx, y, hy, rfl⟩ := hg
  have NJ : ∀ z ∈ (glIwa k n).N, z ∈ V.J n := fun z hz =>
    Subgroup.mem_sup_left (Subgroup.mem_sup_left hz)
  have NmJ : ∀ z ∈ (glIwa k n).Nm V.c, z ∈ V.J n := fun z hz => Subgroup.mem_sup_right hz
  have NKO : ∀ z ∈ (glIwa k n).N, z ∈ KO k (Fin n) := fun z hz => hz.2
  have NmKO : ∀ c, ∀ z ∈ (glIwa k n).Nm c, z ∈ KO k (Fin n) := fun c z hz =>
    Subgroup.map_le_range _ _ hz.2
  have hh : y * σ x ∈ V.J n := mul_mem hy (map_mem_j_of_pres V σ hσ x hx)
  have key : ∀ u : (glIwa k n).N, ∃ a ∈ (glIwa k n).N, ∃ s ∈ V.TH n, ∃ b ∈ (glIwa k n).Nm V.c,
      y * σ x * σ (u : GL (Fin n) k) = a * s * b := fun u =>
    (factJ k V n).1 _ (mul_mem hh (NJ _ (hσ.N _ u.2)))
  choose a ha s hs b hb hab using key
  let Ψ : (glIwa k n).N → (glIwa k n).N := fun u =>
    ⟨dg d * a u * (dg d)⁻¹,
      ((shrink k n d hd 0).1 (a u) (ha u) (mem_kc_zero_of_mem_ko _ (NKO _ (ha u)))).1⟩
  obtain ⟨u, hu⟩ := fixPt k n (glIwa k n).N (Or.inl rfl) Ψ (by
    intro m u1 u2 h12
    have e1 : (y * σ x * σ (u1 : GL (Fin n) k))⁻¹ * (y * σ x * σ (u2 : GL (Fin n) k)) =
        σ ((u1 : GL (Fin n) k)⁻¹ * u2) := by
      rw [map_mul, map_inv]
      group
    have h1 : (a u1 * s u1 * b u1)⁻¹ * (a u2 * s u2 * b u2) ∈ Kc k n m := by
      rw [← hab, ← hab, e1]
      exact hσ.K m _ h12
    have h2 := (factJ k V n).2 m _ (ha u1) _ (ha u2) _ (hs u1) _ (hs u2) _ (hb u1) _ (hb u2) h1
    have h3 := ((shrink k n d hd m).1 _ (mul_mem (inv_mem (ha u1)) (ha u2)) h2).2
    have e2 : ((Ψ u1 : GL (Fin n) k))⁻¹ * (Ψ u2 : GL (Fin n) k) =
        dg d * ((a u1)⁻¹ * a u2) * (dg d)⁻¹ := by
      simp only [Ψ]
      group
    rw [e2]
    exact h3)
  have hu' : dg d * a u * (dg d)⁻¹ = (u : GL (Fin n) k) := congrArg Subtype.val hu
  have ht := mem_ko_and_torus_of_mem_th V _ (hs u)
  have tinvT : (s u)⁻¹ ∈ (glIwa k n).T := inv_mem ht.2
  have memΨ : ∀ w ∈ (glIwa k n).Nm V.c,
      (b u)⁻¹ * ((s u)⁻¹ * ((dg d)⁻¹ * σ w * dg d) * s u) ∈ (glIwa k n).Nm V.c := by
    intro w hw
    refine mul_mem (inv_mem (hb u)) ?_
    have h1 := ((shrink k n d hd 0).2 V.c (σ w) (hσ.Nm _ _ hw)
      (mem_kc_zero_of_mem_ko _ (NmKO _ _ (hσ.Nm _ _ hw)))).1
    have h2 := (glIwa k n).T_Nm V.c _ tinvT _ h1
    rwa [inv_inv] at h2
  let Ψ₂ : (glIwa k n).Nm V.c → (glIwa k n).Nm V.c := fun w => ⟨_, memΨ w w.2⟩
  obtain ⟨w, hw⟩ := fixPt k n ((glIwa k n).Nm V.c) (Or.inr ⟨V.c, rfl⟩) Ψ₂ (by
    intro m w1 w2 h12
    have e : ((Ψ₂ w1 : GL (Fin n) k))⁻¹ * (Ψ₂ w2 : GL (Fin n) k) =
        (s u)⁻¹ * ((dg d)⁻¹ * σ ((w1 : GL (Fin n) k)⁻¹ * w2) * dg d) * ((s u)⁻¹)⁻¹ := by
      simp only [Ψ₂]
      rw [map_mul, map_inv]
      group
    rw [e]
    refine conj_mem_kc_of_mem_ko _ _ _ (inv_mem ht.1) ?_
    have hmem : σ ((w1 : GL (Fin n) k)⁻¹ * w2) ∈ (glIwa k n).Nm V.c :=
      hσ.Nm _ _ (mul_mem (inv_mem w1.2) w2.2)
    exact ((shrink k n d hd m).2 V.c _ hmem (hσ.K m _ h12)).2)
  have hw' : (b u)⁻¹ * ((s u)⁻¹ * ((dg d)⁻¹ * σ w * dg d) * s u) = (w : GL (Fin n) k) :=
    congrArg Subtype.val hw
  have comm : dg d * s u = s u * dg d :=
    (glIwa k n).comm _ ⟨d, rfl⟩ _ ((glIwa k n).T_le ht.2)
  refine ⟨x * u * σ w, mul_mem (mul_mem hx (NJ _ u.2)) (NmJ _ (hσ.Nm _ _ w.2)), s u, hs u, ?_⟩
  rw [map_mul, map_mul, hσ.invol]
  have E0 : (x * (u : GL (Fin n) k) * σ w)⁻¹ * (x * dg d * y) * (σ x * σ (u : GL (Fin n) k) * w) =
      (σ w)⁻¹ * ((u : GL (Fin n) k)⁻¹ * dg d * (y * σ x * σ (u : GL (Fin n) k)) * w) := by
    group
  have E4 : b u * (w : GL (Fin n) k) = (s u)⁻¹ * ((dg d)⁻¹ * σ w * dg d) * s u := by
    conv_lhs => rw [← hw']
    group
  rw [E0, hab u, ← hu']
  have E5 : (dg d * a u * (dg d)⁻¹)⁻¹ * dg d * (a u * s u * b u) * (w : GL (Fin n) k) =
      dg d * s u * (b u * w) := by
    group
  rw [E5, E4, ← comm]
  group

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.MemNOfJ
noncomputable section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

namespace UpperTheory.V.Z.Sym.Sig

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem ord_le_ord_of_valuation_le {x y : kˣ} (h : valuation k (x : k) ≤ valuation k (y : k)) : ord k y ≤ ord k x := by
  rw [val_ord, val_ord] at h
  exact (zpow_le_zpow_iff_right_of_lt_one₀ GlAx.unif_pos ValuativeRel.uniformizer_lt_one).1 h

private theorem ord_anti {d : Fin n → kˣ} (hd : Dom d) : Antitone fun i => ord k (d i) := fun i j hij => ord_le_ord_of_valuation_le (hd i j hij)

private theorem conjN {d : Fin n → kˣ} (hd : Dom d) {x : GL (Fin n) k} (hx : x ∈ (glIwa k n).N) :
    dg d * x * (dg d)⁻¹ ∈ (glIwa k n).N :=
  GlAx.conj_N (fun i => val_ord (d i)) (ord_anti hd) hx

private theorem conjNm {d : Fin n → kˣ} (hd : Dom d) {c : ℕ} {y : GL (Fin n) k} (hy : y ∈ (glIwa k n).Nm c) :
    (dg d)⁻¹ * y * dg d ∈ (glIwa k n).Nm c := by
  have h := GlAx.conj_Nm (t := d⁻¹) (a := fun i => ord k ((d⁻¹) i)) (fun i => val_ord _) (c := c) (c' := c) ?_ hy
  · rw [map_inv, inv_inv] at h
    exact h
  · intro i j hji
    have h1 : valuation k ((d j : k)) ≤ valuation k (d i : k) := hd j i hji.le
    have h2 : valuation k (((d⁻¹) i : kˣ) : k) ≤ valuation k (((d⁻¹) j : kˣ) : k) := by
      simp only [Pi.inv_apply, Units.val_inv_eq_inv_val, map_inv₀]
      exact inv_anti₀ (zero_lt_iff.2 (by simp)) h1
    have h3 := ord_le_ord_of_valuation_le h2
    omega

private theorem DC_left (V : Lev k) {d : Fin n → kˣ} {j x : GL (Fin n) k} (hj : j ∈ V.J n) (hx : x ∈ V.DC d) :
    j * x ∈ V.DC d := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  exact ⟨j * a, (V.J n).mul_mem hj ha, b, hb, by simp only [mul_assoc]⟩

private theorem DC_N (V : Lev k) {d : Fin n → kˣ} (hd : Dom d) {g : GL (Fin n) k} (hg : g ∈ V.DC d) :
    ∃ a ∈ (glIwa k n).N, ∃ b ∈ V.J n, g = a * dg d * b := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hg
  obtain ⟨a', ha', s, hs, b', hb', rfl⟩ := (factJ k V n).1 a ha
  obtain ⟨t, -, hts⟩ := Subgroup.mem_map.1 hs
  have hcomm : s * dg d = dg d * s := by
    rw [← hts]
    show diagT k (Fin n) t * diagT k (Fin n) d = diagT k (Fin n) d * diagT k (Fin n) t
    rw [← map_mul, ← map_mul, mul_comm]
  refine ⟨a', ha', s * ((dg d)⁻¹ * b' * dg d) * b, ?_, ?_⟩
  · exact (V.J n).mul_mem ((V.J n).mul_mem (V.TH_le hs) (V.Nm_le (conjNm hd hb'))) hb
  · calc a' * s * b' * dg d * b = a' * (s * dg d) * (dg d)⁻¹ * b' * dg d * b := by group
      _ = a' * (dg d * s) * (dg d)⁻¹ * b' * dg d * b := by rw [hcomm]
      _ = a' * dg d * (s * ((dg d)⁻¹ * b' * dg d) * b) := by group

private theorem dom_mul {d d' : Fin n → kˣ} (hd : Dom d) (hd' : Dom d') : Dom (d * d') := fun i j h => by
  simp only [Pi.mul_apply, Units.val_mul, map_mul]
  exact mul_le_mul' (hd i j h) (hd' i j h)

private theorem dg_mul (d d' : Fin n → kˣ) : dg (d * d') = dg d * dg d' := map_mul _ d d'

private theorem key (V : Lev k) {d d' : Fin n → kˣ} (hd : Dom d) (hd' : Dom d') {n₁ n₂ g : GL (Fin n) k}
    (h₁ : n₁ ∈ (glIwa k n).N) (h₂ : n₂ ∈ (glIwa k n).N)
    (g₁ : (n₁ * dg d)⁻¹ * g ∈ V.DC d') (g₂ : (n₂ * dg d)⁻¹ * g ∈ V.DC d') :
    (n₁ * dg d)⁻¹ * (n₂ * dg d) ∈ V.J n := by
  obtain ⟨x, hxdef⟩ : ∃ x, x = (n₁ * dg d)⁻¹ * (n₂ * dg d) := ⟨_, rfl⟩
  rw [← hxdef]
  obtain ⟨a₁, ha₁, b₁, hb₁, e₁⟩ := DC_N V hd' g₁
  obtain ⟨a₂, ha₂, b₂, hb₂, e₂⟩ := DC_N V hd' g₂
  have hx : x = a₁ * dg d' * (b₁ * b₂⁻¹) * (dg d')⁻¹ * a₂⁻¹ := by
    have h0 : x = ((n₁ * dg d)⁻¹ * g) * ((n₂ * dg d)⁻¹ * g)⁻¹ := by rw [hxdef]; group
    rw [h0, e₁, e₂]
    group
  have hxu : x ∈ unipB k (Fin n) := by
    have hu : n₁⁻¹ * n₂ ∈ unipB k (Fin n) :=
      (glIwa k n).N_le ((glIwa k n).N.mul_mem ((glIwa k n).N.inv_mem h₁) h₂)
    have h0 := GlAx.conj_up (d⁻¹) hu
    rw [map_inv, inv_inv] at h0
    have h3 : x = (diagT k (Fin n) d)⁻¹ * (n₁⁻¹ * n₂) * diagT k (Fin n) d := by rw [hxdef]; group
    rw [h3]
    exact h0
  have hw : (dg d')⁻¹ * (a₁⁻¹ * x * a₂) * dg d' = b₁ * b₂⁻¹ := by rw [hx]; group
  have hwu : (dg d')⁻¹ * (a₁⁻¹ * x * a₂) * dg d' ∈ unipB k (Fin n) := by
    have h0 : a₁⁻¹ * x * a₂ ∈ unipB k (Fin n) :=
      (unipB k (Fin n)).mul_mem ((unipB k (Fin n)).mul_mem
        ((unipB k (Fin n)).inv_mem ((glIwa k n).N_le ha₁)) hxu) ((glIwa k n).N_le ha₂)
    have h3 := GlAx.conj_up (d'⁻¹) h0
    rw [map_inv, inv_inv] at h3
    exact h3
  obtain ⟨α, hα, s, hs, γ, hγ, eβ⟩ :=
    (factJ k V n).1 (b₁ * b₂⁻¹) ((V.J n).mul_mem hb₁ ((V.J n).inv_mem hb₂))
  obtain ⟨t, -, rfl⟩ := Subgroup.mem_map.1 hs
  rw [hw, eβ] at hwu
  have hγ0 : γ ∈ Subgroup.comap (GlobalTheory.CuspRep.invT n k) (unipB k (Fin n)) ⊓ Kc k n (V.c + 1) := hγ
  have hu2 := GlAx.uniq t ((unipB k (Fin n)).mul_mem ((unipB k (Fin n)).inv_mem hwu)
    ((glIwa k n).N_le hα)) (Subgroup.mem_inf.1 hγ0).1 (by group)
  have eα : α * diagT k (Fin n) t * γ = α := inv_mul_eq_one.1 hu2.1
  have key2 : a₁⁻¹ * x * a₂ = dg d' * α * (dg d')⁻¹ := by
    have h0 : (dg d')⁻¹ * (a₁⁻¹ * x * a₂) * dg d' = α := by rw [hw, eβ, eα]
    rw [← h0]
    group
  have hxN : x ∈ (glIwa k n).N := by
    have h0 : x = a₁ * (dg d' * α * (dg d')⁻¹) * a₂⁻¹ := by rw [← key2]; group
    rw [h0]
    exact (glIwa k n).N.mul_mem ((glIwa k n).N.mul_mem ha₁ (conjN hd' hα)) ((glIwa k n).N.inv_mem ha₂)
  exact V.N_le hxN

end UpperTheory.V.Z.Sym.Sig

open UpperTheory.V.Z.Sym.Sig in
theorem UpperTheory.V.Z.Sym.Sig.dCMul :
    UpperTheory.V.Z.Sym.Sig.DCMul := by
  intro k _ _ _ _ V n d d' hd hd' g
  have gen : ∀ p q : GL (Fin n) k, p ∈ V.DC d → p⁻¹ * g ∈ V.DC d' → q ∈ V.DC d → q⁻¹ * g ∈ V.DC d' →
      p⁻¹ * q ∈ V.J n := by
    intro p q hp hpg hq hqg
    obtain ⟨n₁, hn₁, b₁, hb₁, rfl⟩ := DC_N V hd hp
    obtain ⟨n₂, hn₂, b₂, hb₂, rfl⟩ := DC_N V hd hq
    have k1 : (n₁ * dg d)⁻¹ * g ∈ V.DC d' := by
      have e : (n₁ * dg d)⁻¹ * g = b₁ * ((n₁ * dg d * b₁)⁻¹ * g) := by group
      rw [e]
      exact DC_left V hb₁ hpg
    have k2 : (n₂ * dg d)⁻¹ * g ∈ V.DC d' := by
      have e : (n₂ * dg d)⁻¹ * g = b₂ * ((n₂ * dg d * b₂)⁻¹ * g) := by group
      rw [e]
      exact DC_left V hb₂ hqg
    have h0 := key V hd hd' hn₁ hn₂ k1 k2
    have e : (n₁ * dg d * b₁)⁻¹ * (n₂ * dg d * b₂) = b₁⁻¹ * ((n₁ * dg d)⁻¹ * (n₂ * dg d)) * b₂ := by group
    rw [e]
    exact (V.J n).mul_mem ((V.J n).mul_mem ((V.J n).inv_mem hb₁) h0) hb₂
  refine ⟨fun hg => ?_, fun y hy hyg => ?_⟩
  · obtain ⟨a, ha, b, hb, hgab⟩ := DC_N V (dom_mul hd hd') hg
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (V.J n) (a * dg d)
    have P0 : (QuotientGroup.mk (a * dg d) : GL (Fin n) k ⧸ V.J n).out ∈ V.DC d ∧
        (QuotientGroup.mk (a * dg d) : GL (Fin n) k ⧸ V.J n).out⁻¹ * g ∈ V.DC d' := by
      rw [hh]
      refine ⟨⟨a, V.N_le ha, h, h.2, rfl⟩, ⟨(h : GL (Fin n) k)⁻¹, (V.J n).inv_mem h.2, b, hb, ?_⟩⟩
      rw [hgab, dg_mul]
      group
    refine ⟨QuotientGroup.mk (a * dg d), P0, fun y hy => ?_⟩
    rw [← Quotient.out_eq y, ← Quotient.out_eq (QuotientGroup.mk (a * dg d) : GL (Fin n) k ⧸ V.J n)]
    exact Quotient.sound (QuotientGroup.leftRel_apply.2 (gen _ _ hy.1 hy.2 P0.1 P0.2))
  · obtain ⟨a, ha, b, hb, rfl⟩ := hy
    obtain ⟨a', ha', b', hb', e⟩ := hyg
    obtain ⟨α, hα, s, hs, γ, hγ, eβ⟩ := (factJ k V n).1 (b * a') ((V.J n).mul_mem hb ha')
    obtain ⟨t, -, rfl⟩ := Subgroup.mem_map.1 hs
    have hcomm : diagT k (Fin n) t * dg d' = dg d' * diagT k (Fin n) t := by
      show diagT k (Fin n) t * diagT k (Fin n) d' = diagT k (Fin n) d' * diagT k (Fin n) t
      rw [← map_mul, ← map_mul, mul_comm]
    have h2 : diagT k (Fin n) t = dg d' * diagT k (Fin n) t * (dg d')⁻¹ := by
      rw [← hcomm]
      group
    have hg : g = a * dg d * (b * a') * dg d' * b' := by
      have h0 : g = (a * dg d * b) * ((a * dg d * b)⁻¹ * g) := by group
      rw [h0, e]
      group
    rw [hg, eβ]
    refine ⟨a * (dg d * α * (dg d)⁻¹), (V.J n).mul_mem ha (V.N_le (conjN hd hα)),
      diagT k (Fin n) t * ((dg d')⁻¹ * γ * dg d') * b',
      (V.J n).mul_mem ((V.J n).mul_mem (V.TH_le hs) (V.Nm_le (conjNm hd' hγ))) hb', ?_⟩
    rw [dg_mul]
    nth_rewrite 1 [h2]
    group

end
end
