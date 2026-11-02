/-!
# 倉庫番のルール仕様（信頼の核）

このファイルだけを読めば「クリア可能」が何を意味するかがわかるように書いてある。
ゲームの実行系（`Leankoban.Engine`）や探索ツールは、ここで定めた関係に対して
健全であることが `Leankoban.Soundness` で証明される。

* 依存するのは Lean core の `Nat`、`List`、`Option`、`String`（バイト列）だけ。
* 盤面は XSB 形式の文字列で与え、ASCII バイト単位で読む（`String.toList` は使わない）。
-/

namespace Leankoban

/-- 盤面上の位置 `(行, 列)`。左上が `(0, 0)`。 -/
abbrev Pos := Nat × Nat

/-- 移動方向。LURD 記法の `u` `d` `l` `r` に対応する。 -/
inductive Dir where
  | U | D | L | R
  deriving DecidableEq, Repr, Inhabited

/-- `p` から方向 `d` へ 1 マス進んだ位置。盤の上端・左端より外へは進めない（`none`）。 -/
def Pos.next : Pos → Dir → Option Pos
  | (r, c), .U => if r = 0 then none else some (r - 1, c)
  | (r, c), .D => some (r + 1, c)
  | (r, c), .L => if c = 0 then none else some (r, c - 1)
  | (r, c), .R => some (r, c + 1)

/-- 盤面。`floor` は人と箱が乗れるマス全体（ゴール・箱・人の初期位置を含む）。
`floor` に含まれないマスはすべて壁として扱う。 -/
structure Level where
  floor  : List Pos
  goals  : List Pos
  boxes  : List Pos
  player : Pos
  deriving Repr, Inhabited

namespace Level

/-- 1 行分のバイト列を読む。
XSB の文字のうち `' '` `'-'` `'_'` `'.'` `'$'` `'*'` `'@'` `'+'` を床とし、
それ以外（`'#'` を含む未知の文字）はすべて壁とみなす。未知の文字を壁と読むのは、
盤面を難しくする方向にしか働かないので、安全側の読み方である。 -/
def scanRow (r : Nat) : Nat → List UInt8 → Level → Level
  | _, [], L => L
  | c, b :: rest, L =>
    let p : Pos := (r, c)
    let n := b.toNat
    -- 32 ' '  45 '-'  95 '_'  46 '.'  36 '$'  42 '*'  64 '@'  43 '+'
    let isFloor := n == 32 || n == 45 || n == 95 || n == 46 || n == 36 || n == 42 || n == 64 || n == 43
    let isGoal := n == 46 || n == 42 || n == 43
    let isBox := n == 36 || n == 42
    let isPlayer := n == 64 || n == 43
    let L := if isFloor then { L with floor := p :: L.floor } else L
    let L := if isGoal then { L with goals := p :: L.goals } else L
    let L := if isBox then { L with boxes := p :: L.boxes } else L
    let L := if isPlayer then { L with player := p } else L
    scanRow r (c + 1) rest L

/-- 行の並びを上から順に読む。 -/
def scanRows : Nat → List String → Level → Level
  | _, [], L => L
  | r, row :: rest, L => scanRows (r + 1) rest (scanRow r 0 row.toByteArray.data.toList L)

/-- XSB 形式の行の並びから盤面を作る。 -/
def ofRows (rows : List String) : Level :=
  scanRows 0 rows ⟨[], [], [], (0, 0)⟩

end Level

/-- 局面：人の位置と箱の位置。 -/
structure State where
  player : Pos
  boxes  : List Pos
  deriving Repr, Inhabited

/-- 盤面の初期局面。 -/
def Level.init (L : Level) : State := ⟨L.player, L.boxes⟩

/-- 1 手の遷移。

* `walk`：進む先が床で、箱がなければ人だけが進む。
* `push`：進む先が床で箱があり、その先が床で箱がなければ、箱を 1 マス押して人も進む。

これ以外の手（壁に当たる、箱を 2 個押す、箱を引く）は存在しない。 -/
inductive Step (L : Level) : State → State → Prop where
  | walk {p : Pos} {bs : List Pos} {d : Dir} {t : Pos} :
      p.next d = some t → t ∈ L.floor → t ∉ bs →
      Step L ⟨p, bs⟩ ⟨t, bs⟩
  | push {p : Pos} {bs : List Pos} {d : Dir} {t u : Pos} :
      p.next d = some t → t ∈ L.floor → t ∈ bs →
      t.next d = some u → u ∈ L.floor → u ∉ bs →
      Step L ⟨p, bs⟩ ⟨t, u :: bs.erase t⟩

/-- 0 手以上の遷移で到達できる。 -/
inductive Reachable (L : Level) : State → State → Prop where
  | refl {s : State} : Reachable L s s
  | step {s t u : State} : Step L s t → Reachable L t u → Reachable L s u

/-- クリア状態：すべての箱がゴール上にあり、すべてのゴールに箱がある。 -/
def Solved (L : Level) (s : State) : Prop :=
  (∀ b ∈ s.boxes, b ∈ L.goals) ∧ (∀ g ∈ L.goals, g ∈ s.boxes)

/-- 盤面としてまともであること（「箱が 0 個なので自明にクリア」のような退化を除く）：
ゴールが 1 個以上あり、箱とゴールが同数で、重複がなく、人が床の上にいて箱と重ならない。 -/
def WellFormed (L : Level) : Prop :=
  0 < L.goals.length ∧ L.goals.length = L.boxes.length ∧
  L.boxes.Nodup ∧ L.goals.Nodup ∧ L.player ∈ L.floor ∧ L.player ∉ L.boxes

/-- クリア可能：初期局面からクリア状態へ到達できる。 -/
def Solvable (L : Level) : Prop :=
  ∃ s, Reachable L L.init s ∧ Solved L s

end Leankoban
