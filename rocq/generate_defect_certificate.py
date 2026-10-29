"""Generate a Rocq certificate; all bounds are re-proved by the Rocq kernel."""
from dataclasses import dataclass
from fractions import Fraction as F
from math import isqrt
from pathlib import Path

SCALE = 10**26


def down(x):
    return F(x.numerator * SCALE // x.denominator, SCALE)


def up(x):
    return -down(-x)


def rf(x):
    if x.denominator == 1:
        return str(x.numerator) if x >= 0 else f"({x.numerator})"
    return f"({x.numerator}/{x.denominator})"


@dataclass
class Node:
    index: int
    op: str
    children: tuple
    lo: F
    hi: F
    invbox: tuple | None = None

    @property
    def name(self):
        return "alpha" if self.op == "alpha" else f"t{self.index}"

    @property
    def fact(self):
        return "Halpha" if self.op == "alpha" else f"H{self.index}"


nodes = []
memo = {}


def make(op, *args):
    key = (op,) + tuple(x.index if isinstance(x, Node) else x for x in args)
    if key in memo:
        return memo[key]
    invbox = None
    if op == "const":
        lo = hi = F(args[0])
        children = ()
    elif op == "alpha":
        lo = F(100801689041906829488, 10**18)
        hi = F(100801689041906829489, 10**18)
        children = ()
    else:
        children = args
        x = args[0]
        if op == "neg":
            lo, hi = -x.hi, -x.lo
        elif op == "add":
            y = args[1]
            lo, hi = x.lo + y.lo, x.hi + y.hi
        elif op == "sub":
            y = args[1]
            lo, hi = x.lo - y.hi, x.hi - y.lo
        elif op in ("mul", "square"):
            y = x if op == "square" else args[1]
            corners = [x.lo*y.lo, x.lo*y.hi, x.hi*y.lo, x.hi*y.hi]
            lo, hi = down(min(corners)), up(max(corners))
        elif op == "sqrt":
            assert x.lo >= 0
            l = isqrt(x.lo.numerator*SCALE*SCALE//x.lo.denominator)
            h = isqrt(x.hi.numerator*SCALE*SCALE//x.hi.denominator)
            lo = F(l, SCALE)
            hi = F(h, SCALE) if F(h, SCALE)**2 == x.hi else F(h+1, SCALE)
        elif op in ("inv", "div"):
            y = x if op == "inv" else args[1]
            assert y.lo > 0, (op, y.index, y.lo, y.hi)
            il, ih = down(1/y.hi), up(1/y.lo)
            invbox = il, ih
            if op == "inv":
                lo, hi = il, ih
            else:
                corners = [x.lo*il, x.lo*ih, x.hi*il, x.hi*ih]
                lo, hi = down(min(corners)), up(max(corners))
        else:
            raise ValueError(op)
    n = Node(len(nodes), op, children, lo, hi, invbox)
    nodes.append(n)
    memo[key] = n
    return n


def c(x): return make("const", F(x))
def add(x,y): return make("add", x,y)
def sub(x,y): return make("sub", x,y)
def mul(x,y): return make("mul", x,y)
def div(x,y): return make("div", x,y)
def inv(x): return make("inv", x)
def sqrt(x): return make("sqrt", x)
def square(x): return make("square", x)
def neg(x): return make("neg", x)


def mm(a,b):
    return [[add(mul(a[i][0],b[0][j]),mul(a[i][1],b[1][j])) for j in range(2)] for i in range(2)]


def sm(r,a): return [[mul(r,x) for x in row] for row in a]
def adj(a): return [[a[1][1],neg(a[0][1])],[neg(a[1][0]),a[0][0]]]
def power(a,n): return [[c(1),c(0)],[c(0),c(1)]] if n == 0 else mm(a,power(a,n-1))
def da(x,y): return sub(sub(c(101),x),mul(c(10),y))
def db(x,y): return add(sub(c(101),x),mul(c(10),y))
def pa(x,y): return div(sub(c(10),y),da(x,y)),div(c(1),da(x,y))
def pb(x,y): return div(add(c(10),y),db(x,y)),div(c(-1),db(x,y))
def ma(x,y): return sm(inv(sqrt(da(x,y))),[[sub(c(10),y),sub(x,c(1))],[c(1),c(10)]])
def mb(x,y): return sm(inv(sqrt(db(x,y))),[[add(c(10),y),sub(c(1),x)],[c(-1),c(10)]])


alpha = make("alpha")
u = sub(div(c(10),alpha),div(c(1),square(alpha))),div(c(1),alpha)
v = pb(*u)
w = pa(*v)
A = sm(inv(sqrt(alpha)), [[sub(c(10),div(c(1),alpha)),
                         sub(add(c(-1),div(c(10),alpha)),div(c(1),square(alpha)))],
                        [c(1),c(10)]])
T = mm(ma(*w),mm(ma(*v),mb(*u)))
D = mm(power(adj(A),2),T)
AD, DA = mm(A,D),mm(D,A)
result = add(AD[1][0],mul(c(-1),DA[1][0]))
assert result.lo > F(1,10000), (result.lo, result.hi)

reachable = set()


def visit(n):
    if n.index in reachable:
        return
    for k in n.children:
        visit(k)
    reachable.add(n.index)


visit(result)


def expr(n):
    if n.op == "const": return rf(n.lo)
    x = n.children[0].name
    if n.op == "sqrt": return f"sqrt {x}"
    if n.op == "square": return f"({x}^2)"
    if n.op == "inv": return f"/{x}"
    if n.op == "neg": return f"(-{x})"
    y = n.children[1].name
    return f"({x} {dict(add='+',sub='-',mul='*',div='/')[n.op]} {y})"


def mul_rule(x,y,lo,hi,ybox=None,yfact=None):
    yl,yh = ybox if ybox else (y.lo,y.hi)
    yf = yfact if yfact else y.fact
    yn = f"(/{y.name})" if ybox else y.name
    return (f"apply (@box_multiply {x.name} {yn} {rf(x.lo)} {rf(x.hi)} "
            f"{rf(yl)} {rf(yh)} {rf(lo)} {rf(hi)}); "
            f"[exact {x.fact}|exact {yf}|nra|nra|nra|nra|nra|nra|nra|nra].")


out = ["(* Generated by generate_defect_certificate.py; checked using only Stdlib. *)",
       "From Stdlib Require Import Reals Psatz.",
       "From HallRay Require Import MatrixAlgebra FiberProducts ReturnBranches ConstantReturn DefectLimit ConstantCoding RealIntervals.",
       "Open Scope R_scope.",
       "",
       "Theorem finite_defect_commutator_certificate : forall alpha,",
       "  100 < alpha -> cubic alpha = 0 ->",
       "  1/10000 < a21 (sub2",
       "    (mul2 (constant_matrix alpha) (explicit_defect_two alpha))",
       "    (mul2 (explicit_defect_two alpha) (constant_matrix alpha))).",
       "Proof.",
       "  intros alpha Ha Hf.",
       "  pose proof (constant_root_fine_isolation alpha Ha Hf) as Hroot.",
       f"  assert (Halpha : {rf(alpha.lo)} <= alpha <= {rf(alpha.hi)}) by lra."]

for n in nodes:
    if n.index not in reachable or n.op == "alpha":
        continue
    out += [f"  set ({n.name} := {expr(n)}).",
            f"  assert ({n.fact} : {rf(n.lo)} <= {n.name} <= {rf(n.hi)}).",
            f"  {{ unfold {n.name}."]
    if n.op == "const":
        out.append("    split; apply Rle_refl.")
    elif n.op == "neg":
        out.append(f"    pose proof {n.children[0].fact}. split; lra.")
    elif n.op in ("add","sub"):
        x,y = n.children
        rule = "box_add" if n.op == "add" else "box_subtract"
        out.append(f"    apply (@{rule} {x.name} {y.name} {rf(x.lo)} {rf(x.hi)} "
                   f"{rf(y.lo)} {rf(y.hi)} {rf(n.lo)} {rf(n.hi)}); "
                   f"[exact {x.fact}|exact {y.fact}|nra|nra].")
    elif n.op == "mul":
        out.append("    " + mul_rule(*n.children,n.lo,n.hi))
    elif n.op == "square":
        x, = n.children
        out.append(f"    apply (@box_square {x.name} {rf(x.lo)} {rf(x.hi)} {rf(n.lo)} {rf(n.hi)}); "
                   f"[exact {x.fact}|nra|nra|nra|nra|nra|nra|nra|nra].")
    elif n.op == "sqrt":
        x, = n.children
        out.append(f"    apply (@box_sqrt {x.name} {rf(x.lo)} {rf(x.hi)} {rf(n.lo)} {rf(n.hi)}); "
                   f"[nra|exact {x.fact}|nra|nra|nra|nra].")
    elif n.op == "inv":
        x, = n.children
        out.append(f"    apply (@box_inverse {x.name} {rf(x.lo)} {rf(x.hi)} {rf(n.lo)} {rf(n.hi)}); "
                   f"[nra|exact {x.fact}|nra|nra|nra|nra].")
    elif n.op == "div":
        x,y = n.children
        il,ih = n.invbox
        out.append(f"    assert (HI : {rf(il)} <= /{y.name} <= {rf(ih)}).")
        out.append(f"    {{ apply (@box_inverse {y.name} {rf(y.lo)} {rf(y.hi)} {rf(il)} {rf(ih)}); "
                   f"[nra|exact {y.fact}|nra|nra|nra|nra]. }}")
        out.append("    " + mul_rule(x,y,n.lo,n.hi,(il,ih),"HI"))
    out.append("  }")

out += ["  assert (Hresult : a21 (sub2",
        "    (mul2 (constant_matrix alpha) (explicit_defect_two alpha))",
        f"    (mul2 (explicit_defect_two alpha) (constant_matrix alpha))) = {result.name}).",
        "  { cbv [constant_matrix explicit_defect_two explicit_defect_product_two matrix_power",
        "      mul2 adj2 sub2 add2 scale2 numerator_a numerator_b normalized_a normalized_b",
        "      fixed_u1 fixed_u2 defect_u1 defect_u2 preceding_u1 preceding_u2",
        "      phi_a1 phi_a2 phi_b1 phi_b2 da db a11 a12 a21 a22 pow",
        "      " + " ".join(n.name for n in nodes if n.index in reachable and n.op != "alpha") + "].",
        "    reflexivity. }", "  rewrite Hresult. lra.", "Qed.", ""]
Path(__file__).with_name("DefectCertificate.v").write_text("\n".join(out))
print(f"Generated {len(reachable)} interval nodes; enclosure [{float(result.lo)}, {float(result.hi)}].")
