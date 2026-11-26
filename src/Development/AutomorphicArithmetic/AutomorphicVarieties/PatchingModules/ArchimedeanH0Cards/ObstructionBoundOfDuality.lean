module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.OdCount
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.DualBound
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ImgCard
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ExistsCore
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.Transl

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.OdLam
open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

theorem UpperTheory.V.Pa.B2.odLam :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (X : Type) [CommRing X] [Algebra x.A X] (X'' : Type) [CommRing X''] [Algebra x.A X''] (D D'' : Dat x.A (plOf G)) (_ : IsOd h x X D) (_ : IsOd h x X'' D'') (g : D.Hom D''), Function.Surjective g.f → (∀ u, UrAx l (L.Ju u)) → ∀ w, ∀ y'' ∈ D''.abelian₂ w, ∃ y ∈ D.abelian₂ w, ∀ s, g.fq w (y s) = y'' s := by
  intro l _ L G G0 h n x X _ _ X'' _ _ D D'' o o'' g hg hur w y'' hy
  have hs : ∀ w, Function.Surjective (g.fq w) := by
    intro w q
    obtain ⟨m, rfl⟩ := D''.surj w q
    obtain ⟨m, rfl⟩ := hg m
    exact ⟨D.π w m, g.comm w m⟩
  have top : ∀ w, (∀ s, s ∈ (plOf G).J w) → ∀ y'' ∈ D''.abelian₂ w, ∃ y ∈ D.abelian₂ w, ∀ s, g.fq w (y s) = y'' s := by
    rintro w hw y'' ⟨-, Y, hY⟩
    obtain ⟨Y, rfl⟩ := hs _ Y
    refine ⟨d0 (D.Q w).ρ Y, ⟨coboundaries_le_cocycles _ (D.Q w).cont ⟨Y, rfl⟩, Y, fun s _ => amitsur_d0_apply _ _ _⟩, fun s => ?_⟩
    rw [hY s (hw s), amitsur_d0_apply, map_sub, g.equivq]
  rcases w with v | u
  · exact top (inV G v) (fun s => Subgroup.mem_top (G := L.Gv v) s) y'' hy
  · obtain ⟨hz, Y, hY⟩ := hy
    obtain ⟨-, k1, k2⟩ := odKill l L G G0 h n x X D o
    obtain ⟨-, -, k3⟩ := odKill l L G G0 h n x X'' D'' o''
    obtain ⟨y, a1, a2, a3⟩ := (hur u x.A (D.Q (inU G u)) (k1 _) (k2 u)).2 (D''.Q (inU G u)) (g.fq (inU G u))
      (g.equivq (inU G u)) (hs _) y'' hz (fun s hs => (hY s hs).trans (sub_eq_zero.2 (k3 u s hs Y)))
    exact ⟨y, ⟨a1, 0, fun s hs => (a2 s hs).trans (sub_eq_zero.2 (k2 u s hs 0)).symm⟩, a3⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.OdSESInv
open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

private theorem map_algebraMap_mul_mul_map_linearMap {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) {Y Z : Type} [CommRing Y] [Algebra x.A Y] [CommRing Z] [Algebra x.A Z] (u : Y →ₗ[x.A] Z) (P Q : Matrix (Fin n) (Fin n) x.A) (N : Matrix (Fin n) (Fin n) Y) :
    (P.map (algebraMap x.A Y) * N * Q.map (algebraMap x.A Y)).map u = P.map (algebraMap x.A Z) * N.map u * Q.map (algebraMap x.A Z) := by
  have key : ∀ (p q : x.A) (y : Y), u (algebraMap x.A Y p * y * algebraMap x.A Y q) = algebraMap x.A Z p * u y * algebraMap x.A Z q := by
    intro p q y
    have h1 : algebraMap x.A Y p * y * algebraMap x.A Y q = (p * q) • y := by
      rw [Algebra.smul_def, map_mul]; ring
    have h2 : algebraMap x.A Z p * u y * algebraMap x.A Z q = (p * q) • u y := by
      rw [Algebra.smul_def, map_mul]; ring
    rw [h1, h2, map_smul]
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.map_apply, Matrix.mul_apply, Finset.sum_mul, map_sum]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => key _ _ _

private theorem exists_matrix_map_eq_of_zero_on_of_mem_range {n : ℕ} {R Y Z : Type} [CommRing R] [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z] (w : Y →ₗ[R] Z) (S : Fin n → Fin n → Prop) (N : Matrix (Fin n) (Fin n) Z) (h0 : ∀ i j, S i j → N i j = 0) (hr : ∀ i j, ¬ S i j → N i j ∈ Set.range w) :
    ∃ N' : Matrix (Fin n) (Fin n) Y, (∀ i j, S i j → N' i j = 0) ∧ N'.map w = N := by
  classical
  refine ⟨Matrix.of fun i j => if h : S i j then 0 else (hr i j h).choose, ?_, ?_⟩
  · intro i j hij
    simp [hij]
  · ext i j
    by_cases hij : S i j
    · simp [hij, h0 i j hij]
    · simp [hij, (hr i j hij).choose_spec]

private theorem mem_od_iff_entry_eq_zero_of_same_block {A R : Type} [CommRing A] [CommRing R] [Algebra A R] {n a : ℕ} (N : Matrix (Fin n) (Fin n) R) :
    N ∈ Od A R n a ↔ ∀ i j : Fin n, ((i : ℕ) < a ↔ (j : ℕ) < a) → N i j = 0 := by
  constructor
  · intro hN i j hij
    exact (Submodule.mem_bot _).1 ((hN i j).1 hij)
  · intro hN i j
    exact ⟨fun hij => (Submodule.mem_bot _).2 (hN i j hij), fun _ => Submodule.mem_top⟩

private theorem inv_w_entry_eq_zero_of_ty_ne_lt_a {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (v : F.Vl) (j k : Fin n) (hjk : x.ty v j ≠ decide ((k : ℕ) < x.a)) :
    (((x.w v)⁻¹ : GL (Fin n) (PowerSeries x.K)) : Matrix (Fin n) (Fin n) (PowerSeries x.K)) j k = 0 := by
  classical
  set W : Matrix (Fin n) (Fin n) (PowerSeries x.K) := ((x.w v : GL (Fin n) (PowerSeries x.K)) : Matrix (Fin n) (Fin n) (PowerSeries x.K)) with hW
  set B : Matrix (Fin n) (Fin n) (PowerSeries x.K) := (((x.w v)⁻¹ : GL (Fin n) (PowerSeries x.K)) : Matrix (Fin n) (Fin n) (PowerSeries x.K)) with hB
  have hBW : B * W = 1 := Units.inv_mul (x.w v)
  have hWB : W * B = 1 := Units.mul_inv (x.w v)
  let β : Bool → PowerSeries x.K := fun b => if b then 1 else 0
  have hpat : W * Matrix.diagonal (fun j : Fin n => β (x.ty v j)) = Matrix.diagonal (fun i : Fin n => β (decide ((i : ℕ) < x.a))) * W := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases h : decide ((i : ℕ) < x.a) = x.ty v j
    · rw [h]; ring_nf
    · rw [show W i j = 0 from x.w_blk v i j h]; simp
  have key : Matrix.diagonal (fun j : Fin n => β (x.ty v j)) * B = B * Matrix.diagonal (fun i : Fin n => β (decide ((i : ℕ) < x.a))) := by
    calc Matrix.diagonal (fun j : Fin n => β (x.ty v j)) * B = B * W * Matrix.diagonal (fun j : Fin n => β (x.ty v j)) * B := by
          rw [hBW, Matrix.one_mul]
      _ = B * (W * Matrix.diagonal (fun j : Fin n => β (x.ty v j))) * B := by rw [Matrix.mul_assoc B]
      _ = B * Matrix.diagonal (fun i : Fin n => β (decide ((i : ℕ) < x.a))) * (W * B) := by
          rw [hpat]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hWB, Matrix.mul_one]
  have e := congrArg (fun M : Matrix (Fin n) (Fin n) (PowerSeries x.K) => M j k) key
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at e
  change B j k = 0
  cases h1 : x.ty v j <;> cases h2 : decide ((k : ℕ) < x.a) <;> simp only [h1, h2, β] at e hjk <;> simp_all

private theorem wiX_mul_mul_wX_eq_zero_of_ty_eq {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (v : F.Vl) {Y : Type} [CommRing Y] [Algebra x.A Y] (N : Matrix (Fin n) (Fin n) Y) (hN : ∀ k l : Fin n, ((k : ℕ) < x.a ↔ (l : ℕ) < x.a) → N k l = 0) (i j : Fin n) (hij : x.ty v i = x.ty v j) :
    (x.wiX Y v * N * x.wX Y v) i j = 0 := by
  simp only [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases h1 : x.ty v i = decide ((k : ℕ) < x.a)
  · by_cases h2 : decide ((l : ℕ) < x.a) = x.ty v j
    · rw [hN k l (decide_eq_decide.mp (by rw [← h1, hij, ← h2]))]; simp
    · simp [NP.wX, x.w_blk v l j h2]
  · simp only [NP.wiX, Matrix.map_apply]
    rw [inv_w_entry_eq_zero_of_ty_ne_lt_a x v i k h1]; simp

private theorem wX_mul_mul_wiX_eq_zero_of_same_block {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (v : F.Vl) {Y : Type} [CommRing Y] [Algebra x.A Y] (P : Matrix (Fin n) (Fin n) Y) (hP : ∀ k l : Fin n, x.ty v k = x.ty v l → P k l = 0) (i j : Fin n) (hij : ((i : ℕ) < x.a ↔ (j : ℕ) < x.a)) :
    (x.wX Y v * P * x.wiX Y v) i j = 0 := by
  simp only [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases h1 : decide ((i : ℕ) < x.a) = x.ty v k
  · by_cases h2 : x.ty v l = decide ((j : ℕ) < x.a)
    · rw [hP k l (by rw [← h1, h2]; exact decide_eq_decide.mpr hij)]; simp
    · simp only [NP.wiX, Matrix.map_apply]
      rw [inv_w_entry_eq_zero_of_ty_ne_lt_a x v l j h2]; simp
  · simp [NP.wX, x.w_blk v i k h1]

private theorem map_wiX_mul_mul_wX_and_wX_mul_mul_wiX {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (v : F.Vl) {Y Z : Type} [CommRing Y] [Algebra x.A Y] [CommRing Z] [Algebra x.A Z] (u : Y →ₗ[x.A] Z) (N : Matrix (Fin n) (Fin n) Y) :
    (x.wiX Y v * N * x.wX Y v).map u = x.wiX Z v * N.map u * x.wX Z v ∧
      (x.wX Y v * N * x.wiX Y v).map u = x.wX Z v * N.map u * x.wiX Z v := by
  unfold NP.wX NP.wiX
  exact ⟨map_algebraMap_mul_mul_map_linearMap x u _ _ N, map_algebraMap_mul_mul_map_linearMap x u _ _ N⟩

private theorem wiX_mul_wX_eq_one_and_wX_mul_wiX_eq_one {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (v : F.Vl) {Y : Type} [CommRing Y] [Algebra x.A Y] :
    x.wiX Y v * x.wX Y v = 1 ∧ x.wX Y v * x.wiX Y v = 1 := by
  unfold NP.wX NP.wiX
  constructor
  · rw [← Matrix.map_mul, Units.inv_mul]; simp
  · rw [← Matrix.map_mul, Units.mul_inv]; simp

theorem UpperTheory.V.Pa.B2.odSES :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (X' : Type) [CommRing X'] [Algebra x.A X'] (X : Type) [CommRing X] [Algebra x.A X] (X'' : Type) [CommRing X''] [Algebra x.A X''] (D' D D'' : Dat x.A (plOf G)) (o' : IsOd h x X' D') (o : IsOd h x X D) (o'' : IsOd h x X'' D'') (u : X' →ₗ[x.A] X) (v : X →ₗ[x.A] X'') (f : D'.Hom D) (g : D.Hom D''), Induced o' o u f → Induced o o'' v g → Function.Injective u → Function.Exact u v → Function.Surjective v → Dat.SES f g := by
  intro l _ L G G0 h n x X' _ _ X _ _ X'' _ _ D' D D'' o' o o'' u v f g hf hg hu hex hv
  have inj : Function.Injective f.f := by
    intro m1 m2 h12
    apply o'.e.injective
    apply Subtype.ext
    have e1 := hf m1
    rw [h12, hf m2] at e1
    ext i j
    exact hu (by simpa using congrArg (fun M : Matrix (Fin n) (Fin n) X => M i j) e1.symm)
  have ex : Function.Exact f.f g.f := by
    intro m
    constructor
    · intro hgm
      have h0 : (↑(o.e m) : Matrix (Fin n) (Fin n) X).map v = 0 := by
        rw [← hg m, hgm]; simp
      obtain ⟨N', hN'0, hN'⟩ := exists_matrix_map_eq_of_zero_on_of_mem_range u (fun i j : Fin n => ((i : ℕ) < x.a ↔ (j : ℕ) < x.a)) (↑(o.e m))
        (fun i j hij => (mem_od_iff_entry_eq_zero_of_same_block _).1 (o.e m).2 i j hij)
        (fun i j _ => (hex _).1 (by simpa using congrArg (fun M : Matrix (Fin n) (Fin n) X'' => M i j) h0))
      refine ⟨o'.e.symm ⟨N', (mem_od_iff_entry_eq_zero_of_same_block _).2 hN'0⟩, ?_⟩
      apply o.e.injective
      apply Subtype.ext
      rw [hf, LinearEquiv.apply_symm_apply]
      exact hN'
    · rintro ⟨m', rfl⟩
      apply o''.e.injective
      apply Subtype.ext
      rw [hg, hf, map_zero]
      ext i j
      simpa using (hex _).2 ⟨_, rfl⟩
  have surj : Function.Surjective g.f := by
    intro m''
    obtain ⟨N, hN0, hN⟩ := exists_matrix_map_eq_of_zero_on_of_mem_range v (fun i j : Fin n => ((i : ℕ) < x.a ↔ (j : ℕ) < x.a)) (↑(o''.e m''))
      (fun i j hij => (mem_od_iff_entry_eq_zero_of_same_block _).1 (o''.e m'').2 i j hij) (fun i j _ => hv _)
    refine ⟨o.e.symm ⟨N, (mem_od_iff_entry_eq_zero_of_same_block _).2 hN0⟩, ?_⟩
    apply o''.e.injective
    apply Subtype.ext
    rw [hg, LinearEquiv.apply_symm_apply]
    exact hN
  refine ⟨inj, ex, surj, ?_, ?_⟩
  · intro w
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨m, rfl⟩ := D'.surj w q
    rw [f.comm] at hq
    rcases w with w | w
    · rw [o'.kerV]
      rw [o.kerV] at hq
      intro i j hji
      have e := hq i j hji
      rw [hf, ← (map_wiX_mul_mul_wX_and_wX_mul_mul_wiX x w u _).1, Matrix.map_apply] at e
      exact hu (by rw [map_zero]; exact e)
    · have h1 : f.f m = 0 := o.kerU w (by rw [hq, map_zero])
      rw [inj (h1.trans (map_zero f.f).symm), map_zero]
  · intro w q
    constructor
    · intro hq
      obtain ⟨m, rfl⟩ := D.surj w q
      rw [g.comm] at hq
      rcases w with w | w
      · have hlow := (o''.kerV w (g.f m)).1 hq
        obtain ⟨P, hP0, hP⟩ := exists_matrix_map_eq_of_zero_on_of_mem_range v (fun i j : Fin n => j < i ∨ x.ty w i = x.ty w j)
          (x.wiX X'' w * (↑(o''.e (g.f m)) : Matrix (Fin n) (Fin n) X'') * x.wX X'' w)
          (fun i j hij => hij.elim (hlow i j) (wiX_mul_mul_wX_eq_zero_of_ty_eq x w _ ((mem_od_iff_entry_eq_zero_of_same_block _).1 (o''.e (g.f m)).2) i j))
          (fun i j _ => hv _)
        have hN : x.wX X w * P * x.wiX X w ∈ Od x.A X n x.a :=
          (mem_od_iff_entry_eq_zero_of_same_block _).2 (fun i j hij => wX_mul_mul_wiX_eq_zero_of_same_block x w P (fun k l hkl => hP0 k l (Or.inr hkl)) i j hij)
        obtain ⟨h1, h2⟩ := wiX_mul_wX_eq_one_and_wX_mul_wiX_eq_one x w (Y := X)
        obtain ⟨h1'', h2''⟩ := wiX_mul_wX_eq_one_and_wX_mul_wiX_eq_one x w (Y := X'')
        have hconj : x.wiX X w * (↑(o.e (o.e.symm ⟨_, hN⟩)) : Matrix (Fin n) (Fin n) X) * x.wX X w = P := by
          rw [LinearEquiv.apply_symm_apply]
          show x.wiX X w * (x.wX X w * P * x.wiX X w) * x.wX X w = P
          simp only [Matrix.mul_assoc, h1, Matrix.mul_one]
          rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
        have hk : D.π (Sum.inl w) (o.e.symm ⟨_, hN⟩) = 0 :=
          (o.kerV w _).2 (fun i j hji => by rw [hconj]; exact hP0 i j (Or.inl hji))
        have hg0 : g.f (o.e.symm ⟨_, hN⟩) = g.f m := by
          apply o''.e.injective
          apply Subtype.ext
          rw [hg (o.e.symm ⟨_, hN⟩), LinearEquiv.apply_symm_apply]
          show (x.wX X w * P * x.wiX X w).map v = _
          rw [(map_wiX_mul_mul_wX_and_wX_mul_mul_wiX x w v P).2, hP]
          simp only [Matrix.mul_assoc, h2'', Matrix.mul_one]
          rw [← Matrix.mul_assoc, h2'', Matrix.one_mul]
        have hdiff : g.f (m - o.e.symm ⟨_, hN⟩) = 0 := by rw [map_sub, hg0, sub_self]
        obtain ⟨m', hm'⟩ := (ex _).1 hdiff
        refine ⟨D'.π _ m', (f.comm _ m').trans ?_⟩
        rw [hm', map_sub, hk, sub_zero]
      · have h1 : g.f m = 0 := o''.kerU w (by rw [hq, map_zero])
        obtain ⟨m', hm'⟩ := (ex m).1 h1
        exact ⟨D'.π _ m', (f.comm _ m').trans (congrArg _ hm')⟩
    · rintro ⟨q', rfl⟩
      obtain ⟨m', rfl⟩ := D'.surj w q'
      rw [f.comm, g.comm, (ex (f.f m')).2 ⟨m', rfl⟩, map_zero]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ExactMid
open ReciprocityTheory.Gal UpperTheory.V.Pa UpperTheory.V.Pa.B2

section SlopeTestRemainingChoices

variable {A Γ : Type} [CommRing A] [Group Γ] [TopologicalSpace Γ] {P : Pl Γ}

private theorem coboundary_mem_cocycles_local [IsTopologicalGroup Γ] (D : Dat A P) {b : D.C2} (hb : b ∈ D.selmerSecondCoboundaries) : b ∈ D.selmerSecondCocycles := by
  obtain ⟨x, hx, h1, h2⟩ := hb
  have hc : ∀ s t : Γ, b.1 (s, t) = D.M.ρ s (x t) - x (s * t) + x s := by
    intro s t
    rw [h1]
    exact d1_apply _ _ _ _
  refine ⟨⟨?_, ?_⟩, fun w => ⟨?_, ?_⟩⟩
  · have e : b.1 = fun q : Γ × Γ => D.M.ρ q.1 (x q.2) - x (q.1 * q.2) + x q.1 := by
      funext q
      exact hc q.1 q.2
    rw [e]
    have hact : Continuous fun p : Γ × D.M.X => D.M.ρ p.1 p.2 := D.M.cont
    have h3 : Continuous fun q : Γ × Γ => D.M.ρ q.1 (x q.2) :=
      hact.comp (continuous_fst.prodMk (hx.comp continuous_snd))
    exact (h3.sub (hx.comp continuous_mul)).add (hx.comp continuous_fst)
  · intro g h k
    rw [hc, hc, hc, hc]
    simp only [map_sub, map_add (f := _), map_mul, Module.End.mul_apply, mul_assoc]
    abel
  · have hF : Continuous fun g : P.G w => D.π w (x (P.φ w g)) :=
      (continuous_of_discreteTopology (f := D.π w)).comp (hx.comp (P.cont w))
    have hy := (h2 w).1.1
    have := hy.add hF
    simpa using this
  · intro g h
    have hyg := (h2 w).1.2 g h
    simp only [Pi.sub_apply, map_sub] at hyg
    have e : b.2 w (g * h) = b.2 w g - D.π w (x (P.φ w g)) + ((D.Q w).ρ g (b.2 w h)
        - (D.Q w).ρ g (D.π w (x (P.φ w h)))) + D.π w (x (P.φ w (g * h))) := by
      rw [← sub_eq_zero] at hyg ⊢
      rw [← hyg]
      abel
    rw [hc, d1_apply, e, ← (P.φ w).map_mul g h]
    simp only [map_sub, map_add (f := _), D.equiv]
    abel

private theorem coboundary_lift_local_conditions {D D'' : Dat A P} (g : D.Hom D'') (hs : Function.Surjective g.f)
    (hl : ∀ w, ∀ y'' ∈ D''.abelian₂ w, ∃ y ∈ D.abelian₂ w, ∀ s, g.fq w (y s) = y'' s)
    {q : D''.C2} (hq : q ∈ D''.selmerSecondCoboundaries) : ∃ b ∈ D.selmerSecondCoboundaries, g.c2 b = q := by
  obtain ⟨x'', hx'', h1, h2⟩ := hq
  choose s hs' using hs
  have hl' := fun w => hl w _ (h2 w)
  choose y hyL hy using hl'
  have hx : Continuous fun t : Γ => s (x'' t) :=
    (continuous_of_discreteTopology (f := s)).comp hx''
  refine ⟨(d1 D.M.ρ (fun t => s (x'' t)), fun w h => D.π w (s (x'' (P.φ w h))) + y w h),
    ⟨fun t => s (x'' t), hx, rfl, fun w => ?_⟩, ?_⟩
  · convert hyL w using 1
    funext h
    simp
  · refine Prod.ext (funext fun st => ?_) (funext fun w => funext fun h => ?_)
    · obtain ⟨a, c⟩ := st
      show g.f (d1 D.M.ρ (fun t => s (x'' t)) (a, c)) = q.1 (a, c)
      rw [h1, d1_apply, d1_apply]
      simp only [map_sub, map_add (f := _), g.equiv, hs']
    · show g.fq w (D.π w (s (x'' (P.φ w h))) + y w h) = q.2 w h
      rw [map_add (f := _), g.comm, hs', hy w h]
      simp

private theorem cocycle_descends_short_exact {D' D D'' : Dat A P} (f : D'.Hom D) (g : D.Hom D'') (h : Dat.SES f g)
    {p : D.C2} (hp : p ∈ D.selmerSecondCocycles) (h0 : g.c2 p = 0) : ∃ p' ∈ D'.selmerSecondCocycles, f.c2 p' = p := by
  have e1 : ∀ st, g.f (p.1 st) = 0 := fun st => congrFun (congrArg Prod.fst h0) st
  have e2 : ∀ w t, g.fq w (p.2 w t) = 0 := fun w t =>
    congrFun (congrFun (congrArg Prod.snd h0) w) t
  choose a ha using fun st => (h.ex (p.1 st)).1 (e1 st)
  choose c hc using fun w t => (h.exq w (p.2 w t)).1 (e2 w t)
  obtain ⟨⟨hpc, hpcoc⟩, hpw⟩ := hp
  refine ⟨(a, c), ⟨⟨?_, ?_⟩, fun w => ⟨?_, ?_⟩⟩,
    Prod.ext (funext ha) (funext fun w => funext (hc w))⟩
  · have ea : a = fun st => Function.invFun f.f (p.1 st) := funext fun st =>
      h.inj (by rw [ha]; exact (Function.invFun_eq ⟨a st, ha st⟩).symm)
    show Continuous a
    rw [ea]
    exact (continuous_of_discreteTopology (f := Function.invFun f.f)).comp hpc
  · intro u v k
    apply h.inj
    rw [map_zero]
    simp only [map_sub, map_add (f := _), f.equiv, ha]
    exact hpcoc u v k
  · have ec : c w = fun t => Function.invFun (f.fq w) (p.2 w t) := funext fun t =>
      h.injq w (by rw [hc]; exact (Function.invFun_eq ⟨c w t, hc w t⟩).symm)
    show Continuous (c w)
    rw [ec]
    exact (continuous_of_discreteTopology (f := Function.invFun (f.fq w))).comp (hpw w).1
  · intro u v
    apply h.injq w
    rw [f.comm, ha, (hpw w).2 u v, d1_apply, d1_apply]
    simp only [map_sub, map_add (f := _), f.equivq, hc]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Pa.B2.exactMid :
    ∀ (A Γ : Type) [CommRing A] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (P : Pl Γ) (D' D D'' : Dat A P) (f : D'.Hom D) (g : D.Hom D''), Dat.SES f g → (∀ w, ∀ y'' ∈ D''.abelian₂ w, ∃ y ∈ D.abelian₂ w, ∀ s, g.fq w (y s) = y'' s) → LinearMap.ker g.h2 ≤ LinearMap.range f.h2 := by
  intro A Γ _ _ _ _ P D' D D'' f g h hl z hz
  obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [LinearMap.mem_ker, Dat.Hom.h2, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hz
  have hq : g.c2 p.1 ∈ D''.selmerSecondCoboundaries := hz
  obtain ⟨b, hb, hbq⟩ := coboundary_lift_local_conditions g h.surj hl hq
  have hm : p.1 - b ∈ D.selmerSecondCocycles := sub_mem p.2 (coboundary_mem_cocycles_local D hb)
  have h0 : g.c2 (p.1 - b) = 0 := by rw [map_sub, hbq, sub_self]
  obtain ⟨p', hp', hfp⟩ := cocycle_descends_short_exact f g h hm h0
  rw [LinearMap.mem_range]
  refine ⟨Submodule.Quotient.mk ⟨p', hp'⟩, ?_⟩
  rw [Dat.Hom.h2, Submodule.mapQ_apply, Submodule.Quotient.eq]
  show f.c2 p' - p.1 ∈ D.selmerSecondCoboundaries
  rw [hfp, sub_sub_cancel_left]
  exact neg_mem hb
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.CokerBound
open ReciprocityTheory.Gal UpperTheory.V.Pa UpperTheory.V.Pa.B2

section

variable {A Γ : Type} [CommRing A] [Group Γ] [TopologicalSpace Γ]
  {P : Pl Γ} {D0 D D' : Dat A P}

private def Defect (k : D0.Hom D) (r : D.Hom D') (p : D'.C2) (c : ∀ w, Z2 (D0.Q w).ρ) : Prop :=
  ∃ q : D.C2, q.1 ∈ Z2 D.M.ρ ∧ (∀ w, Continuous (q.2 w)) ∧ r.c2 q = p ∧
    ∀ w g h, k.fq w ((c w).1 (g, h)) = D.π w (q.1 (P.φ w g, P.φ w h)) - d1 (D.Q w).ρ (q.2 w) (g, h)

private theorem defect_sub {k : D0.Hom D} {r : D.Hom D'} {p p' : D'.C2} {c c' : ∀ w, Z2 (D0.Q w).ρ}
    (h : Defect k r p c) (h' : Defect k r p' c') : Defect k r (p - p') (c - c') := by
  obtain ⟨q, hq1, hq2, hq3, hq4⟩ := h
  obtain ⟨q', hq1', hq2', hq3', hq4'⟩ := h'
  refine ⟨q - q', Submodule.sub_mem _ hq1 hq1', fun w => (hq2 w).sub (hq2' w),
    by rw [map_sub, hq3, hq3'], fun w g h => ?_⟩
  have e1 := hq4 w g h
  have e2 := hq4' w g h
  simp only [Pi.sub_apply, Submodule.coe_sub, AddSubgroupClass.coe_sub, Prod.fst_sub,
    Prod.snd_sub, map_sub] at e1 e2 ⊢
  rw [e1, e2]
  abel

private theorem lift_two_cocycle_surjection [IsTopologicalGroup Γ] (r : D.Hom D') (hs : Function.Surjective r.f)
    (h2 : Function.Surjective (mapH2 D.M.ρ D'.M.ρ r.f continuous_of_discreteTopology r.equiv))
    (z' : Z2 D'.M.ρ) : ∃ z ∈ Z2 D.M.ρ, ∀ s, r.f (z s) = z'.1 s := by
  obtain ⟨y, hy⟩ := h2 (Submodule.Quotient.mk z')
  obtain ⟨z0, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [mapH2, Submodule.mapQ_apply, Submodule.Quotient.eq, Submodule.mem_comap,
    Submodule.coe_subtype, separated_dvr_second_cohomology_mem] at hy
  obtain ⟨b', hb'c, hb'⟩ := hy
  choose σ hσ using hs
  let b : Γ → D.M.X := fun g => σ (b' g)
  have hbc : Continuous b := (continuous_of_discreteTopology (f := σ)).comp hb'c
  refine ⟨z0.1 - d1 D.M.ρ b, ?_, fun s => ?_⟩
  · exact Submodule.sub_mem _ z0.2 (coboundaries2_le_cocycles2 _ D.M.cont ((separated_dvr_second_cohomology_mem _ _).2 ⟨b, hbc, rfl⟩))
  · obtain ⟨g, h⟩ := s
    have e := congrFun hb' (g, h)
    rw [d1_apply] at e
    change _ = r.f (z0.1 (g, h)) - z'.1 (g, h) at e
    simp only [b, Pi.sub_apply, map_sub, map_add (f := _), d1_apply, r.equiv, hσ]
    rw [e]
    abel

private theorem defect_ex [IsTopologicalGroup Γ] {k : D0.Hom D} {r : D.Hom D'} (S : Dat.SES k r)
    (h2 : Function.Surjective (mapH2 D.M.ρ D'.M.ρ r.f continuous_of_discreteTopology r.equiv))
    (p : D'.selmerSecondCocycles) : ∃ c, Defect k r p.1 c := by
  obtain ⟨hp1, hp2⟩ := p.2
  obtain ⟨z, hz, hzr⟩ := lift_two_cocycle_surjection r S.surj h2 ⟨p.1.1, hp1⟩
  have hfq : ∀ w, Function.Surjective (r.fq w) := by
    intro w y
    obtain ⟨m', rfl⟩ := D'.surj w y
    obtain ⟨m, rfl⟩ := S.surj m'
    exact ⟨D.π w m, r.comm w m⟩
  choose σ hσ using hfq
  let q : D.C2 := (z, fun w g => σ w (p.1.2 w g))
  have hqc : ∀ w, Continuous (q.2 w) := fun w =>
    (continuous_of_discreteTopology (f := σ w)).comp (hp2 w).1
  let e : ∀ w, P.G w × P.G w → (D.Q w).X := fun w s =>
    D.π w (z (P.φ w s.1, P.φ w s.2)) - d1 (D.Q w).ρ (q.2 w) s
  have he : ∀ w s, r.fq w (e w s) = 0 := by
    intro w s
    obtain ⟨g, h⟩ := s
    simp only [e, q, map_sub, map_add (f := _), d1_apply, r.comm, hzr, r.equivq, hσ]
    rw [(hp2 w).2 g h, d1_apply, sub_self]
  have hex : ∀ w s, ∃ x, k.fq w x = e w s := fun w s => (S.exq w (e w s)).mp (he w s)
  let τ : ∀ w, (D.Q w).X → (D0.Q w).X := fun w => Function.invFun (k.fq w)
  have hτ : ∀ w s, k.fq w (τ w (e w s)) = e w s := fun w s => Function.invFun_eq (hex w s)
  have hec : ∀ w, Continuous (e w) := by
    intro w
    have hd : ∀ s : P.G w × P.G w, d1 (D.Q w).ρ (q.2 w) s
        = (D.Q w).ρ s.1 (q.2 w s.2) - q.2 w (s.1 * s.2) + q.2 w s.1 := fun s => d1_apply _ _ s.1 s.2
    have h1 : Continuous fun s : P.G w × P.G w => D.π w (z (P.φ w s.1, P.φ w s.2)) :=
      (continuous_of_discreteTopology (f := D.π w)).comp
        (hz.1.comp (((P.cont w).comp continuous_fst).prodMk ((P.cont w).comp continuous_snd)))
    have h2' : Continuous fun s : P.G w × P.G w => d1 (D.Q w).ρ (q.2 w) s := by
      simp only [hd]
      exact (((D.Q w).cont.comp (continuous_fst.prodMk ((hqc w).comp continuous_snd))).sub
        ((hqc w).comp continuous_mul)).add ((hqc w).comp continuous_fst)
    exact h1.sub h2'
  have hE : ∀ w (g h t : P.G w), (D.Q w).ρ g (e w (h, t)) - e w (g * h, t) + e w (g, h * t)
      - e w (g, h) = 0 := by
    intro w g h t
    have key := congrArg (D.π w) (hz.2 (P.φ w g) (P.φ w h) (P.φ w t))
    simp only [map_sub, map_add (f := _), map_zero, D.equiv] at key
    simp only [e, d1_apply, map_sub, map_add (f := _), map_mul, Module.End.mul_apply, mul_assoc]
    refine (sub_eq_zero.mp ?_).trans key
    abel
  let c : ∀ w, Z2 (D0.Q w).ρ := fun w =>
    ⟨fun s => τ w (e w s), (continuous_of_discreteTopology (f := τ w)).comp (hec w), by
      intro g h t
      apply S.injq w
      simp only [map_sub, map_add (f := _), map_zero, k.equivq, hτ]
      exact hE w g h t⟩
  refine ⟨c, q, hz, hqc, ?_, fun w g h => hτ w (g, h)⟩
  refine Prod.ext ?_ ?_
  · funext s
    exact hzr s
  · funext w g
    exact hσ w _

private theorem defect_zero {k : D0.Hom D} {r : D.Hom D'} (S : Dat.SES k r) (p : D'.selmerSecondCocycles)
    {c : ∀ w, Z2 (D0.Q w).ρ} (h : Defect k r p.1 c)
    (hc : (fun w => (Submodule.Quotient.mk (c w) : H2 (D0.Q w).ρ)) ∈ LinearMap.range D0.loc2) :
    (Submodule.Quotient.mk p : D'.H2LocalConditions) ∈ LinearMap.range r.h2 := by
  obtain ⟨q, hq1, hq2, hq3, hq4⟩ := h
  obtain ⟨y, hy⟩ := hc
  obtain ⟨y0, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have hw : ∀ w, ∃ b : P.G w → (D0.Q w).X, Continuous b ∧ ∀ g h,
      (c w).1 (g, h) = D0.π w (y0.1 (P.φ w g, P.φ w h)) - d1 (D0.Q w).ρ b (g, h) := by
    intro w
    have e := congrFun hy w
    simp only [Dat.loc2, LinearMap.pi_apply, compatiblePairH2, Submodule.mapQ_apply] at e
    rw [Submodule.Quotient.eq, Submodule.mem_comap, Submodule.coe_subtype, separated_dvr_second_cohomology_mem] at e
    obtain ⟨b, hb, hbe⟩ := e
    refine ⟨b, hb, fun g h => ?_⟩
    have e2 := congrFun hbe (g, h)
    change _ = D0.π w (y0.1 (P.φ w g, P.φ w h)) - (c w).1 (g, h) at e2
    rw [e2]
    abel
  choose b hbc hbe using hw
  have hZ : (q.1 - fun s => k.f (y0.1 s), fun w g => q.2 w g - k.fq w (b w g)) ∈ D.selmerSecondCocycles := by
    refine ⟨Submodule.sub_mem _ hq1
      (cocycles2Map D0.M.ρ D.M.ρ k.f continuous_of_discreteTopology k.equiv y0).2,
      fun w => ⟨?_, fun g h => ?_⟩⟩
    · exact (hq2 w).sub ((continuous_of_discreteTopology (f := k.fq w)).comp (hbc w))
    · have e1 := hq4 w g h
      rw [hbe w g h] at e1
      simp only [Pi.sub_apply, map_sub, map_add (f := _), d1_apply, k.comm, k.equivq] at e1 ⊢
      refine sub_eq_zero.mp (Eq.trans ?_ (sub_eq_zero.mpr e1.symm))
      abel
  refine ⟨Submodule.Quotient.mk ⟨_, hZ⟩, ?_⟩
  rw [Dat.Hom.h2, Submodule.mapQ_apply]
  congr 1
  apply Subtype.ext
  change r.c2 _ = p.1
  rw [← hq3]
  refine Prod.ext ?_ ?_
  · funext s
    change r.f (q.1 s - k.f (y0.1 s)) = r.f (q.1 s)
    rw [map_sub, (S.ex _).mpr ⟨_, rfl⟩, sub_zero]
  · funext w g
    change r.fq w (q.2 w g - k.fq w (b w g)) = r.fq w (q.2 w g)
    rw [map_sub, (S.exq w _).mpr ⟨_, rfl⟩, sub_zero]

end

theorem UpperTheory.V.Pa.B2.cokerBound :
    ∀ (A Γ : Type) [CommRing A] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (P : Pl Γ) (D0 D D' : Dat A P) (k : D0.Hom D) (r : D.Hom D'), Dat.SES k r → Function.Surjective (mapH2 D.M.ρ D'.M.ρ r.f continuous_of_discreteTopology r.equiv) → Finite D0.Ck2 → Finite (D'.H2LocalConditions ⧸ LinearMap.range r.h2) ∧ Nat.card (D'.H2LocalConditions ⧸ LinearMap.range r.h2) ≤ Nat.card D0.Ck2 := by
  intro A Γ _ _ _ _ P D0 D D' k r S h2 hfin
  have hp : ∀ a : D'.H2LocalConditions ⧸ LinearMap.range r.h2, ∃ p : D'.selmerSecondCocycles,
      Submodule.Quotient.mk (Submodule.Quotient.mk p : D'.H2LocalConditions) = a := fun a => by
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    exact ⟨p, rfl⟩
  choose p hp using hp
  choose c hc using defect_ex S h2
  have hinj : Function.Injective fun a : D'.H2LocalConditions ⧸ LinearMap.range r.h2 =>
      (Submodule.Quotient.mk (fun w => (Submodule.Quotient.mk (c (p a) w) : H2 (D0.Q w).ρ)) : D0.Ck2) := by
    intro a b hab
    have h1 := (Submodule.Quotient.eq _).1 hab
    have h3 := defect_zero S (p a - p b) (defect_sub (hc (p a)) (hc (p b))) h1
    rw [← hp a, ← hp b]
    exact (Submodule.Quotient.eq _).2 h3
  exact ⟨Finite.of_injective _ hinj, Nat.card_le_card_of_injective _ hinj⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.GenTrick
open IsLocalRing

private theorem card_coker_eq_card_ker {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    [Finite M] (f : M →ₗ[A] M) :
    Nat.card (M ⧸ LinearMap.range f) = Nat.card (LinearMap.ker f) := by
  have h1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.range f)
  have h2 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f)
  have h3 : Nat.card (M ⧸ LinearMap.ker f) = Nat.card (LinearMap.range f) :=
    Nat.card_congr f.quotKerEquivRange.toEquiv
  rw [h3] at h2
  have hpos : 0 < Nat.card (LinearMap.range f) := Nat.card_pos
  rw [h2, mul_comm] at h1
  exact (Nat.eq_of_mul_eq_mul_left hpos h1).symm

private theorem UpperTheory.V.Pa.B2.card_quot_span_pow_irreducible_eq_pow {A : Type} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (t : A) (ht : Irreducible t) (e : ℕ) :
    Nat.card (A ⧸ Ideal.span {t ^ e}) = Nat.card (ResidueField A) ^ e := by
  have hmax := ht.maximalIdeal_eq
  have ht0 : t ≠ 0 := ht.ne_zero
  let J : ℕ → AddSubgroup A := fun k => (Ideal.span {t ^ k}).toAddSubgroup
  have hJ : ∀ k, Nat.card (A ⧸ Ideal.span {t ^ k}) = (J k).index := fun k => rfl
  have h1 : (J 1).index = Nat.card (ResidueField A) := by
    rw [← hJ, pow_one, ← hmax]
    rfl
  rw [hJ]
  induction e with
  | zero =>
    simp [J, Ideal.span_singleton_one, AddSubgroup.index_top]
  | succ e ih =>
    have hle : J (e + 1) ≤ J e := by
      intro x hx
      simp only [J, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton] at hx ⊢
      exact (pow_dvd_pow t (Nat.le_succ e)).trans hx
    have hrel : (J (e + 1)).relIndex (J e) = Nat.card (ResidueField A) := by
      let f : A →+ A := AddMonoidHom.mulLeft (t ^ e)
      have hrange : f.range = J e := by
        ext x
        simp only [f, AddMonoidHom.mem_range, AddMonoidHom.coe_mulLeft, J,
          Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton]
        constructor
        · rintro ⟨a, rfl⟩
          exact dvd_mul_right _ _
        · rintro ⟨a, rfl⟩
          exact ⟨a, rfl⟩
      have hcomap : (J (e + 1)).comap f = J 1 := by
        ext x
        simp only [f, AddSubgroup.mem_comap, AddMonoidHom.coe_mulLeft, J,
          Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton, pow_one]
        rw [pow_succ, mul_dvd_mul_iff_left (pow_ne_zero e ht0)]
      rw [← h1, ← hcomap, AddSubgroup.index_comap, hrange]
    rw [← AddSubgroup.relIndex_mul_index hle, ih, hrel, pow_succ, mul_comm]

theorem UpperTheory.V.Pa.B2.genTrick :
    ∀ (A H : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Finite (ResidueField A)] [AddCommGroup H] [Module A H] [Finite H] (t : A) (g C m : ℕ), Irreducible t → (∀ y : H, t ^ m • y = 0) → (∀ e ≤ m, Nat.card (H ⧸ LinearMap.range (LinearMap.lsmul A H (t ^ e))) ≤ Nat.card (ResidueField A) ^ (g * e + C)) → ∀ ξ : Fin (g + 1) → H, ∃ c : Fin (g + 1) → A, (∃ i, IsUnit (c i)) ∧ t ^ C • ∑ i, c i • ξ i = 0 := by
  intro A H _ _ _ _ _ _ _ t g C m ht hm hcard ξ
  classical
  by_cases hCm : m ≤ C
  · refine ⟨fun _ => 1, ⟨0, isUnit_one⟩, ?_⟩
    have hp : t ^ C = t ^ (C - m) * t ^ m := by
      rw [← pow_add]
      congr 1
      omega
    rw [hp, mul_smul, hm, smul_zero]
  by_contra hne
  push_neg at hne
  set e := C + 1 with he
  have hem : e ≤ m := by omega
  let φ : (Fin (g + 1) → A) →ₗ[A] H := Fintype.linearCombination A ξ
  have hφ : ∀ c, φ c = ∑ i, c i • ξ i := fun c => Fintype.linearCombination_apply A ξ c
  have hmax := ht.maximalIdeal_eq
  have key : ∀ k ≤ e, ∀ d d0 : Fin (g + 1) → A, φ d = t ^ e • φ d0 → ∀ i, t ^ k ∣ d i := by
    intro k
    induction k with
    | zero =>
      intro _ d d0 _ i
      simp
    | succ k ih =>
      intro hk d d0 hd
      choose d' hd' using ih (by omega) d d0 hd
      by_cases hall : ∀ i, t ∣ d' i
      · intro i
        obtain ⟨w, hw⟩ := hall i
        exact ⟨w, by rw [hd' i, hw, pow_succ, mul_assoc]⟩
      · push_neg at hall
        obtain ⟨i0, hi0⟩ := hall
        exfalso
        have hdd : d = t ^ k • d' := funext fun i => by simp [hd' i]
        rw [hdd, map_smul] at hd
        have e1 : t ^ k • φ (d' - t ^ (e - k) • d0) = 0 := by
          rw [map_sub, map_smul, smul_sub, hd, smul_smul, ← pow_add,
            Nat.add_sub_cancel' (by omega : k ≤ e), sub_self]
        apply hne (d' - t ^ (e - k) • d0) ⟨i0, ?_⟩
        · rw [← hφ]
          have hp : t ^ C = t ^ (C - k) * t ^ k := by
            rw [← pow_add]
            congr 1
            omega
          rw [hp, mul_smul, e1, smul_zero]
        · rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ← notMem_maximalIdeal, hmax,
            Ideal.mem_span_singleton]
          intro hdiv
          apply hi0
          have h2 : t ∣ t ^ (e - k) * d0 i0 :=
            Dvd.dvd.mul_right (dvd_pow_self t (by omega : e - k ≠ 0)) _
          simpa using dvd_add hdiv h2
  let N := LinearMap.range φ
  let Q := N ⧸ LinearMap.range (LinearMap.lsmul A N (t ^ e))
  haveI : Finite Q := Finite.of_surjective _ (Submodule.mkQ_surjective _)
  have hsurj : Function.Surjective (Ideal.Quotient.mk (Ideal.span {t ^ e})) :=
    Ideal.Quotient.mk_surjective
  let sec := Function.surjInv hsurj
  let γ : (Fin (g + 1) → A ⧸ Ideal.span {t ^ e}) → Q := fun x =>
    Submodule.Quotient.mk ⟨φ (fun i => sec (x i)), LinearMap.mem_range_self φ _⟩
  have hinj : Function.Injective γ := by
    intro x y hxy
    have h1 := (Submodule.Quotient.eq _).mp hxy
    obtain ⟨n, hn⟩ := LinearMap.mem_range.mp h1
    obtain ⟨d0, hd0⟩ := LinearMap.mem_range.mp n.2
    have hd : φ ((fun i => sec (x i)) - (fun i => sec (y i))) = t ^ e • φ d0 := by
      rw [hd0, map_sub]
      have := congrArg Subtype.val hn
      simpa using this.symm
    funext i
    have hdv := key e le_rfl _ d0 hd i
    rw [← Function.surjInv_eq hsurj (x i), ← Function.surjInv_eq hsurj (y i)]
    exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr (by simpa using hdv))
  have hQ : Nat.card (Fin (g + 1) → A ⧸ Ideal.span {t ^ e}) ≤ Nat.card Q :=
    Nat.card_le_card_of_injective γ hinj
  rw [Nat.card_fun, Nat.card_fin, UpperTheory.V.Pa.B2.card_quot_span_pow_irreducible_eq_pow t ht e] at hQ
  have hQN : Nat.card Q = Nat.card (LinearMap.ker (LinearMap.lsmul A N (t ^ e))) :=
    card_coker_eq_card_ker _
  have hker : Nat.card (LinearMap.ker (LinearMap.lsmul A N (t ^ e))) ≤
      Nat.card (LinearMap.ker (LinearMap.lsmul A H (t ^ e))) := by
    refine Nat.card_le_card_of_injective
      (fun x => ⟨x.1.1, by
        have := x.2
        simp only [LinearMap.mem_ker, LinearMap.lsmul_apply] at this ⊢
        exact congrArg Subtype.val this⟩) ?_
    intro x y hxy
    have hv := congrArg Subtype.val hxy
    apply Subtype.ext
    apply Subtype.ext
    simpa using hv
  have hH : Nat.card (LinearMap.ker (LinearMap.lsmul A H (t ^ e))) =
      Nat.card (H ⧸ LinearMap.range (LinearMap.lsmul A H (t ^ e))) :=
    (card_coker_eq_card_ker _).symm
  have hb := hcard e hem
  have hq : 1 < Nat.card (ResidueField A) := Finite.one_lt_card
  have hlt : Nat.card (ResidueField A) ^ (g * e + C) < (Nat.card (ResidueField A) ^ e) ^ (g + 1) := by
    rw [← pow_mul]
    exact Nat.pow_lt_pow_right hq (by rw [he]; ring_nf; omega)
  omega
end

open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.W IsLocalRing

namespace UpperTheory.V.Pa.B2

private theorem h2_comp_eq_smul_of_comp_eq_smul {A Γ : Type} [CommRing A] [Group Γ] [TopologicalSpace Γ] {P : Pl Γ} {D D' : Dat A P}
    (r : D.Hom D') (f : D'.Hom D) (a : A) (h : ∀ m, f.f (r.f m) = a • m) (y : D.H2LocalConditions) : f.h2 (r.h2 y) = a • y := by
  have hq : ∀ w (q : (D.Q w).X), f.fq w (r.fq w q) = a • q := by
    intro w q
    obtain ⟨m, rfl⟩ := D.surj w q
    rw [r.comm, f.comm, h, map_smul]
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  simp only [Dat.Hom.h2, Submodule.mapQ_apply, ← Submodule.Quotient.mk_smul]
  congr 1
  apply Subtype.ext
  simp only [LinearMap.restrict_apply, Submodule.coe_smul]
  refine Prod.ext ?_ ?_
  · funext s
    exact h _
  · funext w g
    exact hq w _

private theorem smul_H2_local_eq_zero_of_smul_eq_zero {A Γ : Type} [CommRing A] [Group Γ] [TopologicalSpace Γ] {P : Pl Γ} (D : Dat A P)
    (a : A) (h : ∀ m : D.M.X, a • m = 0) (y : D.H2LocalConditions) : a • y = 0 := by
  have hq : ∀ w (q : (D.Q w).X), a • q = 0 := by
    intro w q
    obtain ⟨m, rfl⟩ := D.surj w q
    rw [← map_smul, h, map_zero]
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [← Submodule.Quotient.mk_smul]
  have hz : a • z = 0 := by
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · funext s
      exact h _
    · funext w g
      exact hq w _
  rw [hz, Submodule.Quotient.mk_zero]

private theorem finAm (K : Type) [Field K] [Finite K] (m : ℕ) :
    Finite (PowerSeries K ⧸ Ideal.span {(PowerSeries.X : PowerSeries K) ^ m}) := by
  classical
  let g : (Fin m → K) → PowerSeries K ⧸ Ideal.span {(PowerSeries.X : PowerSeries K) ^ m} :=
    fun c => Ideal.Quotient.mk _ (∑ i : Fin m, c i • (PowerSeries.X : PowerSeries K) ^ (i : ℕ))
  refine Finite.of_surjective g ?_
  intro q
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective q
  refine ⟨fun i => PowerSeries.coeff (i : ℕ) f, ?_⟩
  apply Ideal.Quotient.eq.mpr
  rw [Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
  intro n hn
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, map_sum]
  simp only [PowerSeries.coeff_smul, PowerSeries.coeff_X_pow, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single ⟨n, hn⟩]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro e
    exact hb (Fin.ext e.symm)
  · simp

section
variable {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n}

private theorem smul_eq_zero_of_algebraMap_eq_zero_of_isOd {X : Type} [CommRing X] [Algebra x.A X] {D : Dat x.A (plOf G)} (o : IsOd h x X D) (a : x.A)
    (ha : algebraMap x.A X a = 0) (y : D.M.X) : a • y = 0 := by
  apply o.e.injective
  rw [map_smul, map_zero]
  apply Subtype.ext
  rw [Submodule.coe_smul, Submodule.coe_zero, ← algebraMap_smul X a, ha, zero_smul]

set_option maxHeartbeats 1600000 in
private theorem step {X X' X'' : Type} [CommRing X] [Algebra x.A X] [CommRing X'] [Algebra x.A X'] [CommRing X'']
    [Algebra x.A X''] {D D' D'' : Dat x.A (plOf G)} (o : IsOd h x X D) (o' : IsOd h x X' D') (o'' : IsOd h x X'' D'')
    {d : ℕ} {dv : L.Vl → ℕ} (hA : CohAx G d dv) (a : x.A) [Finite D''.H2LocalConditions] (hF : Finite D''.Ck2)
    (uf : X' →ₗ[x.A] X) (ug : X →ₗ[x.A] X'') (uk : X'' →ₗ[x.A] X) (ur : X →ₗ[x.A] X')
    (i1 : Function.Injective uf) (i2 : Function.Exact uf ug) (i3 : Function.Surjective ug) (i4 : Function.Injective uk)
    (i5 : Function.Exact uk ur) (i6 : Function.Surjective ur) (i7 : ∀ y, uf (ur y) = a • y) :
    Nat.card (D.H2LocalConditions ⧸ LinearMap.range (LinearMap.lsmul x.A D.H2LocalConditions a)) ≤ Nat.card D''.H2LocalConditions * Nat.card D''.Ck2 := by
  obtain ⟨f1, hf1⟩ := odHom _ _ _ _ h _ x _ _ _ _ o' o uf
  obtain ⟨g1, hg1⟩ := odHom _ _ _ _ h _ x _ _ _ _ o o'' ug
  obtain ⟨k1, hk1⟩ := odHom _ _ _ _ h _ x _ _ _ _ o'' o uk
  obtain ⟨r1, hr1⟩ := odHom _ _ _ _ h _ x _ _ _ _ o o' ur
  have s1 := odSES _ _ _ _ h _ x _ _ _ _ _ _ o' o o'' uf ug f1 g1 hf1 hg1 i1 i2 i3
  have s2 := odSES _ _ _ _ h _ x _ _ _ _ _ _ o'' o o' uk ur k1 r1 hk1 hr1 i4 i5 i6
  have hcomp : ∀ m, f1.f (r1.f m) = a • m := by
    intro m
    apply o.e.injective
    apply Subtype.ext
    rw [hf1, hr1, Matrix.map_map, map_smul, Submodule.coe_smul]
    ext i j
    simp [i7]
  have hex : g1.h2.ker ≤ f1.h2.range :=
    exactMid _ _ _ _ _ _ f1 g1 s1 (odLam _ _ _ _ h _ x _ _ _ _ o o'' g1 s1.surj hA.ur)
  have hon : Function.Surjective (mapH2 D.M.ρ D'.M.ρ r1.f (by continuity) r1.equiv) :=
    hA.onto _ D.M D'.M (odKill _ _ _ _ h _ x _ _ o).1 r1.f r1.equiv s2.surj
  obtain ⟨hfin, hcard⟩ := cokerBound _ _ _ _ _ _ k1 r1 s2 hon hF
  have hfr : ∀ y, f1.h2 (r1.h2 y) = a • y := h2_comp_eq_smul_of_comp_eq_smul r1 f1 a hcomp
  set R := LinearMap.range (LinearMap.lsmul x.A D.H2LocalConditions a) with hRdef
  have hRF : R ≤ LinearMap.range f1.h2 := by
    rintro _ ⟨y, rfl⟩
    exact ⟨r1.h2 y, by rw [hfr]; rfl⟩
  rw [← Submodule.card_quotient_mul_card_quotient (LinearMap.range f1.h2) R hRF, mul_comm]
  apply Nat.mul_le_mul
  · have hfk : Finite (D.H2LocalConditions ⧸ LinearMap.ker g1.h2) :=
      Finite.of_equiv _ (LinearMap.quotKerEquivRange g1.h2).toEquiv.symm
    have hs : Function.Surjective ((LinearMap.ker g1.h2).liftQ (LinearMap.range f1.h2).mkQ
        (by rw [Submodule.ker_mkQ]; exact hex)) := by
      intro q
      obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ q
      exact ⟨Submodule.Quotient.mk z, rfl⟩
    calc Nat.card (D.H2LocalConditions ⧸ LinearMap.range f1.h2) ≤ Nat.card (D.H2LocalConditions ⧸ LinearMap.ker g1.h2) :=
          Nat.card_le_card_of_surjective _ hs
      _ = Nat.card (LinearMap.range g1.h2) := Nat.card_congr (LinearMap.quotKerEquivRange g1.h2).toEquiv
      _ ≤ Nat.card D''.H2LocalConditions := Nat.card_le_card_of_injective _ Subtype.val_injective
  · have hker : LinearMap.range r1.h2 ≤ LinearMap.ker (R.mkQ ∘ₗ f1.h2) := by
      rintro _ ⟨y, rfl⟩
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hfr]
      exact ⟨y, rfl⟩
    have hmap : (LinearMap.range f1.h2).map R.mkQ = LinearMap.range ((LinearMap.range r1.h2).liftQ _ hker) := by
      rw [Submodule.range_liftQ, LinearMap.range_comp]
    rw [hmap]
    refine le_trans ?_ hcard
    exact Nat.card_le_card_of_surjective _ (LinearMap.surjective_rangeRestrict _)

end

set_option maxHeartbeats 800000 in
theorem obstructionBound_of_duality : ObstructionBoundFromDuality := by
  intro l _ L G0 T n x k al d hl h0 hN hH hE
  obtain ⟨dv0, hA0⟩ := h0
  obtain ⟨C0, hC0⟩ := sel0 l L G0 n x k d dv0 hl hA0
  obtain ⟨Cn, hCn⟩ := selN l L G0 T n x al hH hE
  obtain ⟨Ch, hCh⟩ := H0_local_card_bounded_of_cls_ker_le_ker l L G0 n x
  obtain ⟨Cd, hCd⟩ := dualBound l L G0 n x
  have hres : Nat.card (ResidueField x.A) = Nat.card x.K :=
    Nat.card_congr PowerSeries.residueFieldOfPowerSeries.toEquiv
  haveI : Finite (ResidueField x.A) := Finite.of_equiv _ PowerSeries.residueFieldOfPowerSeries.toEquiv.symm
  have hzero : ∀ e, algebraMap x.A (x.Am e) (x.t ^ e) = 0 := fun e =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  haveI : ∀ e, Finite (x.Am e) := fun e => finAm x.K e
  refine ⟨C0 + Cn + Ch * Fintype.card L.Vl + 2 * Cd, fun m => ?_⟩
  filter_upwards [hCn m] with N hNm
  intro z hz
  obtain ⟨dvN, hAN⟩ := hN N
  obtain ⟨D, ⟨o⟩⟩ := odEx l L (T.GN N) G0 (T.h N) n x (x.Am m) ⟨m, hzero m⟩
  obtain ⟨ξ, hξ⟩ := transl l L (T.GN N) G0 (T.h N) n x k (x.Am m) D (k.g + 1) z hl ⟨m, hzero m⟩ o hAN.ur hz
  haveI : Finite D.H2LocalConditions := (odCount l L (T.GN N) G0 (T.h N) n x (x.Am m) D d dvN hl o hAN).1
  have hbound : ∀ e ≤ m, Nat.card (D.H2LocalConditions ⧸ LinearMap.range (LinearMap.lsmul x.A D.H2LocalConditions (x.t ^ e))) ≤
      Nat.card (ResidueField x.A) ^ (k.g * e + (C0 + Cn + Ch * Fintype.card L.Vl + 2 * Cd)) := by
    intro e he
    rw [hres]
    obtain ⟨uf, ug, uk, ur, i1, i2, i3, i4, i5, i6, i7⟩ := amMaps x.K e m he
    obtain ⟨D1, ⟨o1⟩⟩ := odEx l L (T.GN N) G0 (T.h N) n x (x.Am (m - e)) ⟨m - e, hzero (m - e)⟩
    obtain ⟨D2, ⟨o2⟩⟩ := odEx l L (T.GN N) G0 (T.h N) n x (x.Am e) ⟨e, hzero e⟩
    obtain ⟨D0, ⟨o0⟩⟩ := odEx l L G0 G0 (Glob.Hom.refl G0) n x (x.Am e) ⟨e, hzero e⟩
    obtain ⟨hf2, hc2, hcnt⟩ := odCount l L (T.GN N) G0 (T.h N) n x (x.Am e) D2 d dvN hl o2 hAN
    haveI := hf2
    have hs := step o o1 o2 hAN (x.t ^ e) hc2 uf ug uk ur i1 i2 i3 i4 i5 i6 i7
    have hck := hAN.ck _ D2 (odKill _ _ _ _ _ _ x _ _ o2).1
    have hsel := hNm e he D2 D0 o2 o0 (hA0.fin _ D0.M (odKill _ _ _ _ _ _ x _ _ o0).1).1
    have hs0 := hC0 e D0 o0
    have hprod : ∏ v, Nat.card (H0 (D2.Q (inV (T.GN N) v)).ρ) ≤ (Nat.card x.K ^ Ch) ^ Fintype.card L.Vl := by
      rw [← Finset.card_univ]
      exact Finset.prod_le_pow_card _ _ _ (fun v _ => hCh (T.GN N) (T.h N) e D2 o2 v)
    have hd := hCd (T.GN N) (T.h N) e D2 o2
    calc _ ≤ Nat.card D2.H2LocalConditions * Nat.card D2.Ck2 := hs
      _ ≤ ((Nat.card x.K ^ (k.g * e + C0) * Nat.card x.K ^ Cn) * (Nat.card x.K ^ Ch) ^ Fintype.card L.Vl
            * Nat.card x.K ^ Cd) * Nat.card x.K ^ Cd := by
          apply Nat.mul_le_mul
          · refine hcnt.trans ?_
            apply Nat.mul_le_mul _ hd
            apply Nat.mul_le_mul _ hprod
            exact hsel.trans (Nat.mul_le_mul_right _ hs0)
          · exact hck.trans hd
      _ = Nat.card x.K ^ (k.g * e + (C0 + Cn + Ch * Fintype.card L.Vl + 2 * Cd)) := by
          rw [← pow_mul]
          simp only [← pow_add]
          congr 1
          ring
  have hkill : ∀ y : D.H2LocalConditions, x.t ^ m • y = 0 := smul_H2_local_eq_zero_of_smul_eq_zero D _ (smul_eq_zero_of_algebraMap_eq_zero_of_isOd o _ (hzero m))
  obtain ⟨c, hcu, hc⟩ := genTrick x.A D.H2LocalConditions x.t k.g (C0 + Cn + Ch * Fintype.card L.Vl + 2 * Cd) m
    PowerSeries.X_irreducible hkill hbound (fun i => Submodule.Quotient.mk (ξ i))
  refine ⟨c, hcu, ?_⟩
  have hmem : ↑(∑ i, (x.t ^ (C0 + Cn + Ch * Fintype.card L.Vl + 2 * Cd) * c i) • ξ i) ∈ D.selmerSecondCoboundaries := by
    have hsum : (∑ i, (x.t ^ (C0 + Cn + Ch * Fintype.card L.Vl + 2 * Cd) * c i) • ξ i) =
        x.t ^ (C0 + Cn + Ch * Fintype.card L.Vl + 2 * Cd) • ∑ i, c i • ξ i := by
      rw [Finset.smul_sum]
      simp only [mul_smul]
    rw [hsum]
    simp only [← Submodule.Quotient.mk_smul] at hc
    have h1 : Submodule.Quotient.mk (p := Submodule.comap D.selmerSecondCocycles.subtype D.selmerSecondCoboundaries)
        (x.t ^ (C0 + Cn + Ch * Fintype.card L.Vl + 2 * Cd) • ∑ i, c i • ξ i) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Submodule.Quotient.mk_smul, ← Submodule.mkQ_apply, map_sum]
      exact hc
    exact Submodule.mem_comap.mp ((Submodule.Quotient.mk_eq_zero (Submodule.comap D.selmerSecondCocycles.subtype D.selmerSecondCoboundaries)).mp h1)
  obtain ⟨Ψ, hΨ, hΨe⟩ := hξ _ hmem
  refine ⟨Ψ, hΨ, fun j γ a b => ?_⟩
  rw [hΨe, Finset.smul_sum]
  simp only [mul_smul]

end UpperTheory.V.Pa.B2
