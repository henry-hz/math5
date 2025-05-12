import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic
import MIL.Common
import Std

open Std
open Lean
open Nat


/-
public interface AExp {}

public class Num implements AExp {
  public int num;
  public Num(int num) {
    this.num = num;
  }
}

public class Var implements AExp {
  public Sring var;
  public Var(String var) {
    this.var = var;
  }
}

public class Add implements AEXp {
  public AExp left;
  public AExp right;
  public Add(AExp left, AExp right) {
    this.right = right;
    this.left = left;
  }
}

public class Sub implements AExt {
  public AExp left;
  public AExp right;
  public Sub(AExp left, AExp right) {
    this.right = right;
    this.left = left;
  }
}

public class Mul implements AExp {
  public AExp left;
  public AExp right;
  public Mul(AExp left, AExp right) {
    this.left = left;
    this.right = right;
  }
}

public class Div implements AExp {
  public left;
  public right;

  public Div(AExp left, AExp right) {
    this.left = left;
    this.right = right;
  }
-/

inductive AExp : Type where
  | num : ℤ → AExp
  | var : String → AExp
  | add : AExp → AExp → AExp
  | sub : AExp → AExp → AExp
  | mul : AExp → AExp → AExp
  | div : AExp → AExp → AExp


  -- 2.1.3 page 25

def a := 2
