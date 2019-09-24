import util

namespace rc_correctness

-- ast defs
def var := ℕ
def const := ℕ
def cnstr := ℕ

inductive expr : Type
| const_app_full (c : const) (ys : list var) : expr
| const_app_part (c : const) (ys : list var) : expr
| var_app (x : var) (y : var) : expr
| ctor (i : cnstr) (ys : list var) : expr
| proj (i : cnstr) (x : var) : expr

inductive fn_body : Type
| ret (x : var) : fn_body 
| «let» (x : var) (e : expr) (F : fn_body) : fn_body
| case (x : var) (Fs : list fn_body) : fn_body
| inc (x : var) (F : fn_body) : fn_body
| dec (x : var) (F : fn_body) : fn_body

structure fn := (ys : list var) (F : fn_body)

inductive rc : Type
| var (x : var) : rc
| const (c : const) : rc
| expr (e : expr) : rc
| fn_body (F : fn_body) : rc
| fn (f : fn) : rc


-- notation
open rc_correctness.expr
open rc_correctness.fn_body

-- expr
notation c `⟦` ys `…` `⟧` := expr.const_app_full c ys
notation c `⟦` ys `…` `, ` `_` `⟧` := expr.const_app_part c ys
notation x `⟦` y `⟧` := expr.var_app x y
notation `⟪` ys `⟫` i := expr.ctor i ys
notation x `[` i `]` := expr.proj i x

-- fn_body
notation x ` ≔ ` e `; ` F := fn_body.let x e F
notation `case ` x ` of ` Fs := fn_body.case x Fs
notation `inc ` x `; ` F := fn_body.inc x F
notation `dec ` x `; ` F := fn_body.dec x F

-- rc
instance var_to_rc : has_coe var rc := ⟨rc.var⟩ 
instance const_to_rc : has_coe var rc := ⟨rc.const⟩ 
instance expr_to_rc : has_coe expr rc := ⟨rc.expr⟩ 
instance fn_body_to_rc : has_coe fn_body rc := ⟨rc.fn_body⟩
instance fn_to_rc : has_coe fn rc := ⟨rc.fn⟩ 


-- fn_body recursor, courtesy of Sebastian Ullrich
def {l} fn_body.rec_wf (C : fn_body → Sort l)
  («ret» : Π (x : var), C (ret x))
  («let» : Π (x : var) (e : expr) (F : fn_body) (F_ih : C F), C (x ≔ e; F))
  («case» : Π (x : var) (Fs : list fn_body) (Fs_ih : ∀ F ∈ Fs, C F), C (case x of Fs))
  («inc» : Π (x : var) (F : fn_body) (F_ih : C F), C (inc x; F))
  («dec» : Π (x : var) (F : fn_body) (F_ih : C F), C (dec x; F)) : Π (x : fn_body), C x
| (fn_body.ret a) := «ret» a
| (x ≔ a; a_1) := «let» x a a_1 (fn_body.rec_wf a_1)
| (case a of a_1) := «case» a a_1 (λ a h, have sizeof a < 1 + sizeof a_1, 
                                            from nat.lt_add_left _ _ _ (list.sizeof_lt_sizeof_of_mem h),
                                          fn_body.rec_wf a)
| (inc a; a_1) := «inc» a a_1 (fn_body.rec_wf a_1)
| (dec a; a_1) := «dec» a a_1 (fn_body.rec_wf a_1)


-- free variables
def FV_expr : expr → finset var
| (c⟦xs…⟧) := xs.to_finset
| (c⟦xs…, _⟧) := xs.to_finset
| (x⟦y⟧) := {x, y}
| (⟪xs⟫i) := xs.to_finset
| (x[i]) := {x}

def FV : fn_body → finset var
| (ret x) := {x}
| (x ≔ e; F) := FV_expr e ∪ ((FV F).erase x)
| (case x of Fs) := insert x (finset.join (Fs.map_wf (λ F h, FV F)))
| (inc x; F) := insert x (FV F)
| (dec x; F) := insert x (FV F)


-- purity
def pure_fn_body' : fn_body → bool 
| (ret x) := true
| (x ≔ e; F) := pure_fn_body' F
| (case x of Fs) := list.all (Fs.map_wf (λ F h, pure_fn_body' F)) id
| (inc x; F) := false
| (dec x; F) := false

def pure_fn_body (F : fn_body) : Prop := pure_fn_body' F

def pure_fn (f : fn) : Prop := pure_fn_body f.F

def pure_program (δ : const → fn) : Prop := ∀ c, pure_fn (δ c)


-- var order
local attribute [reducible] var
abbreviation var_le : var → var → Prop := nat.le
instance var_le_is_trans : is_trans var var_le := ⟨@nat.le_trans⟩
instance var_le_is_antisymm : is_antisymm var var_le := ⟨@nat.le_antisymm⟩
instance var_le_is_total : is_total var var_le := ⟨@nat.le_total⟩
local attribute [semireducible] var


-- repr
-- var
local attribute [reducible] var
instance var_has_repr : has_repr var := ⟨repr⟩
local attribute [semireducible] var

-- const
local attribute [reducible] const
instance const_has_repr : has_repr const := ⟨repr⟩
local attribute [semireducible] const

-- expr
def expr_repr : expr → string
| (c⟦ys…⟧) := c.repr ++ "⟦" ++ ys.repr ++ "…⟧"
| (c⟦ys…, _⟧) := c.repr ++ "⟦" ++ ys.repr ++ "…, _⟧"
| (x⟦y⟧) := x.repr ++ "⟦" ++ y.repr ++ "⟧"
| (⟪ys⟫i) := "⟪" ++ ys.repr ++ "⟫" ++ i.repr 
| (x[i]) := x.repr ++ "[" ++ i.repr ++ "]"

instance expr_has_repr : has_repr expr := ⟨expr_repr⟩ 

-- fn_body
def fn_body_repr : fn_body → string
| (ret x) := "ret " ++ x.repr
| (x ≔ e; F) := x.repr ++ " ≔ " ++ repr e ++ "; " ++ fn_body_repr F
| (case x of Fs) := "case " ++ x.repr ++ " of " ++ (Fs.map_wf (λ F h, fn_body_repr F)).repr
| (inc x; F) := "inc " ++ x.repr ++ "; " ++ fn_body_repr F
| (dec x; F) := "dec " ++ x.repr ++ "; " ++ fn_body_repr F

instance fn_body_has_repr : has_repr fn_body := ⟨fn_body_repr⟩ 

end rc_correctness