# 复现

## 编译稿件

使用 TeX Live 或 MacTeX 的 XeLaTeX，含 CTeX、Fandol、AMS 和 hyperref。

```sh
(cd paper/source && latexmk -xelatex -interaction=nonstopmode -halt-on-error strong-maximal-zh.tex)
(cd paper/source && latexmk -xelatex -interaction=nonstopmode -halt-on-error strong-maximal-en.tex)
```

## 计算材料

[第 148 轮记录](r148/report.md)说明平衡块中位数阶梯算例的范围。仓库提供[原 Wolfram 脚本](r148/check.wls)以及可直接运行的 Python 标准库版本。它检查等分情形中 $1/(2(M+1))$ 的覆盖差。[复算结果](r148/release-check.json)保留了八组精确分数。

```sh
python3 verification/r148/check_staircase.py
```

[技术补充材料](../paper/technical-supplement.html)收录更多原研究记录。在 GitHub 可下载 HTML 后用浏览器打开。

## Lean

```sh
(cd lean && ./verify.sh)
```

`verify.sh` 依次做四件事：拒绝含 `sorry`/`admit`/自设公理的源码；扫描
`StrongMaximal/*.lean` 的**全部**声明并重新生成 `StrongMaximal/Audit.lean`
（因此审计清单不会与源码脱节）；清空 olean 后完整重建；逐条检查
`#print axioms` 输出，出现 `propext`、`Classical.choice`、`Quot.sound`
以外的依赖即失败。

需要 `elan`（工具链由 `lean/lean-toolchain` 固定为 `leanprover/lean4:v4.36.0`，Mathlib 由
`lean/lakefile.lean` + `lean/lake-manifest.json` 固定在 `v4.36.0`）。`build.sh` 按依赖顺序编译
全部模块并输出公理审计。

模块与状态见 [lean/report.md](../lean/report.md)：其中列出「论文公式／定理 → Lean 顶层声明 →
依赖文件 → 完整／条件性／未接入」的逐项对照、未形式化的解析步骤、以及原稿下界 Edgeworth 记账的
一处量级缺口（附数值复核脚本 `lean/lower-bound-audit.py`）。

原 v1.0.0 的有理数分位数引理保留为 [`StrongMaximal/RankRat.lean`](../lean/StrongMaximal/RankRat.lean)，
内容未改写；[公理报告](lean-axioms.txt)仍列出它原本的两条依赖。
