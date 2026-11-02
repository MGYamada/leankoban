import Leankoban.Soundness
import Leankoban.Levels.Data

/-!
# 面 99 の可解性証明

箱 5 個。証明書の解は押し 52 回・手数 155（押し数最小の解）。

この証明が依存するのは、ルール仕様 `Leankoban.Spec`、実行系 `Leankoban.Engine`、
健全性定理 `Leankoban.Soundness.certify`、そしてカーネルによる計算だけで、公理は一切使わない。
（`lake exe genproofs` が自動生成。手で編集しない。）
-/

namespace Leankoban.Proofs.Level099

open Leankoban

/-- ゲームが読み込む盤面 `Levels.level099` を、ここに絵として展開したもの。 -/
theorem board_eq : Levels.level099 = [
    "  ####",
    "  #  #",
    " ##  #####",
    "##       #",
    "#     . +#",
    "#  ### $$#",
    "#######$ #",
    "#   $  $ #",
    "#  ..   .#",
    "#######  #",
    "      ####"] := rfl

/-- 解の手順（LURD 記法。小文字は歩く手、大文字は箱を押す手）。 -/
def solution : String :=
    "DDDLdlluLLdrrrruLLrrruuulldRDrUddLdlluRdllluRRdrrUUUddddrUUluuluurDDDDrd\
    LLLuRllldlluRRRRdrrUUUdddllLrrruuuluurDDDDrdLuuurDuluurDlddrDldLLuRdrUUU\
    luurrdLddrU"

/-- **面 99 はクリア可能である。** -/
theorem solvable :
    WellFormed (Level.ofRows Levels.level099) ∧ Solvable (Level.ofRows Levels.level099) :=
  Soundness.certify Levels.level099 solution (by decide +kernel)

end Leankoban.Proofs.Level099
