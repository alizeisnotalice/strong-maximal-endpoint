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
(cd lean && lean -DwarningAsError=true StrongMaximal.lean)
```

[代码](../lean/StrongMaximal.lean)对应论文“秩的随机演化”一节，在有理数上验证分位数阈值等价及对正分母的约分。[公理报告](lean-axioms.txt)列出依赖。
