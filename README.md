# Endpoint Bounds for the Uncentered Strong Maximal Operator

[Paper (English)](paper/strong-maximal-en.pdf) · [Paper (Chinese)](paper/strong-maximal-zh.pdf) · [Technical supplement](paper/technical-supplement.html) · [Reproduction guide](verification/README.md) · [Citation](#citation)

Zhihao Zheng<sup>1</sup>, Haotian Tang<sup>2</sup>, and Yibo Peng<sup>2</sup>

<sup>1</sup> School of Physics and Astronomy, Beijing Normal University<br>
<sup>2</sup> School of Mathematical Sciences, Beijing Normal University

Let $M_nf(x)$ be the supremum of the Lebesgue averages of $\lvert f\rvert$ over bounded axis-parallel rectangles of positive volume containing $x$. Set $\Phi_n(t)=t(1+\log^+t)^{n-1}$ for $t>0$ and $\Phi_n(0)=0$. We study how the least constant $C_n$ in the following distributional inequality depends on $n$.

$$
\lvert\{x:M_nf(x)>\lambda\}\rvert
\le C_n\int_{\mathbb R^n}\Phi_n(\lvert f(x)\rvert/\lambda)\,dx,\qquad \lambda>0.
$$

## Main results

Let $\mu$ be the positive solution of $\mu=1+e^{-\mu}$. The two-sided bounds in the paper imply

$$
\log C_n=\mu n-\sqrt\mu\,\sqrt{n\log n}+o\bigl(\sqrt{n\log n}\bigr).
$$

At the finer $\log n$ scale, put $d_n=\sqrt{\mu n}\,z_n$, where $z_n>0$ satisfies $\bar\Phi(z_n)=\sqrt{\mu/n}\,z_n$ and $\bar\Phi$ is the standard Gaussian upper tail. The paper proves

$$
\frac{9-\mu}{24}
\le \liminf_{n\to\infty}\frac{\log C_n-\mu n+d_n}{\log n}
\le \limsup_{n\to\infty}\frac{\log C_n-\mu n+d_n}{\log n}
\le \frac{3+\mu}{12}.
$$

The exact coefficient of the logarithmic term remains open for general inputs.

## Reproduction

The repository includes the LaTeX source, a technical supplement, and a script that checks eight exact rational cases of a finite staircase example. The paper and supplement give the estimates for the operator on general inputs. [LaTeX source](paper/source/) · [Reproduction commands](verification/README.md#计算材料)

## Citation

Use the [BibTeX entry](https://github.com/alizeisnotalice/strong-maximal-endpoint/blob/v1.0.0/paper/citation.bib) for the archived paper in [v1.0.0](https://github.com/alizeisnotalice/strong-maximal-endpoint/releases/tag/v1.0.0).
