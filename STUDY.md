# 理論ノート: strict order-only attack

この文書は、Bad Curriculum の strict no-Phase2 profile を、オンライン SGD・局所二次近似・NTK 線形化で定式化する。LSTM 全体に対する無条件の一般定理ではなく、明示した仮定の下での条件付き理論である。

## 1. 固定プールと順序

ラベルを $y\in\{-1,+1\}$、LSTM の binary logit を $f_\theta(x)$ とし、損失を

$$
\ell(\theta;x,y)=\log\left(1+\exp(-y f_\theta(x))\right)
$$

とする。固定データプールを

$$
D=A\cup B,\qquad |A|=90{,}000,\quad |B|=10{,}000
$$

と置く。

- $A$ は Phase 1 の balanced source-label review。
- $B$ は Phase 3 の selector-disagreement review。
- random control と tuned schedule は同一の $D$、同一の source label、同一の vocabulary、同一の初期重み、同一の test set を共有する。
- review の重複、ラベル反転、入力の変更はない。

両条件の違いは permutation だけである。

$$
\pi_{\mathrm{random}}=\operatorname{Shuffle}(D),
\qquad
\pi_{\mathrm{attack}}=\operatorname{Shuffle}(A)\Vert\operatorname{Shuffle}(B).
$$

## 2. Phase 3 の選択

別の source-only selector の logit を $f_s(x)$ とし、その signed margin を

$$
m_s(x,y)=y f_s(x)
$$

と定義する。Phase 3 は selector が高信頼で誤分類する review から構成する。

$$
B_\gamma=
\left\{(x,y)\in D_{\mathrm{train}}\;\middle|\; y f_s(x)\le -\gamma\right\}.
$$

実装は source label $-1,+1$ から各 5,000 件を採用する。訓練ラベルは常に Yelp source label である。

$$
y_{\mathrm{train}}=y_{\mathrm{source}}.
$$

selector の予測を label に使わず、$-y_{\mathrm{source}}$ への反転も行わない。

## 3. Phase 3 gradient の大きさ

cross-entropy gradient は

$$
\nabla_\theta\ell(\theta;x,y)
=-y\,\sigma\left(-y f_\theta(x)\right)\nabla_\theta f_\theta(x)
$$

である。Phase 1 後の target model を $\theta_A$ とし、selector と target model の表現が近いと仮定する。

$$
f_{\theta_A}(x)\approx f_s(x).
$$

$x\in B_\gamma$ では

$$
y f_{\theta_A}(x)\lesssim-\gamma,
$$

ゆえに

$$
\sigma\left(-y f_{\theta_A}(x)\right)\gtrsim\sigma(\gamma).
$$

Phase 1 model が強く逆に予測する review ほど、source label での cross-entropy update は大きい。Phase 3 は label poison ではなく、Phase 1 model が作った feature--label 対応を強く修正する source-label update である。

## 4. NTK 線形化と test margin

Phase 1 後の近傍で

$$
f_{\theta+\Delta\theta}(x')
\approx
f_\theta(x')+\nabla_\theta f_\theta(x')^\top\Delta\theta
$$

と線形化する。NTK を

$$
K_\theta(x',x)=
\nabla_\theta f_\theta(x')^\top\nabla_\theta f_\theta(x)
$$

とすると、Phase 3 example $(x,y)$ の一回の SGD update は

$$
\Delta f(x')
\approx
\eta y\,\sigma\left(-y f_\theta(x)\right)K_\theta(x',x)
$$

となる。

Test signed margin を

$$
M(\theta)=
\mathbb{E}_{(x',y')\sim T}\left[y'f_\theta(x')\right]
$$

と定義する。Phase 3 による期待的な margin 変化は

$$
\Delta M_B
\approx
\eta\,
\mathbb{E}_{(x',y')\sim T,\;(x,y)\sim B}
\left[
 y'y\,
 \sigma\left(-y f_{\theta_A}(x)\right)
 K_{\theta_A}(x',x)
\right].
$$

攻撃に必要な data-dependent condition は

$$
\mathbb{E}_{T,B}
\left[
 y'y\,
 \sigma\left(-y f_{\theta_A}(x)\right)
 K_{\theta_A}(x',x)
\right]<0.
$$

である。Phase 3 review が source label と逆方向の selector representation を持ち、test review と共有する kernel feature が十分にあると、Phase 3 update は test signed margin を負方向へ押す。

十分な Phase 3 update により

$$
M(\theta_A)+\sum_{k=1}^{m}\Delta M_{B,k}<0
$$

となれば、平均 signed margin と test prediction が系統的に反転しうる。

## 5. 順序依存性

Phase 1 / Phase 3 の経験損失を

$$
F_A(\theta)=\mathbb{E}_{A}[\ell(\theta;x,y)],
\qquad
F_B(\theta)=\mathbb{E}_{B}[\ell(\theta;x,y)]
$$

とする。random schedule は small-step limit で概ね

$$
F_{\mathrm{mix}}(\theta)=0.9F_A(\theta)+0.1F_B(\theta)
$$

の最適化に対応する。一方、attack schedule は有限時間 update map の合成である。

$$
\theta_{\mathrm{attack}}
\approx
\Phi_B^m\circ\Phi_A^n(\theta_0).
$$

一般に

$$
\Phi_B^m\circ\Phi_A^n\ne
\Phi_A^n\circ\Phi_B^m.
$$

gradient field $g_A=\nabla F_A$, $g_B=\nabla F_B$ を用いれば、順序効果は Lie bracket

$$
[g_A,g_B](\theta)
=J_{g_B}(\theta)g_A(\theta)-J_{g_A}(\theta)g_B(\theta)
$$

が非ゼロであることに対応する。

$$
[g_A,g_B](\theta)\ne0.
$$

loss が非線形で、training 中に representation 自体が変化する neural network では通常この条件が成立する。gradient が定数の線形問題では、同じ sample multiset の順序だけではこの現象は生じない。

## 6. 局所二次近似

Phase 1 / Phase 3 loss を局所的に

$$
F_A(\theta)
\approx
\frac12(\theta-\theta_A^\star)^\top H_A(\theta-\theta_A^\star),
$$

$$
F_B(\theta)
\approx
\frac12(\theta-\theta_B^\star)^\top H_B(\theta-\theta_B^\star)
$$

と近似する。Phase 1 が $\theta_A^\star$ 近傍まで到達後、Phase 3 を $m$ step 実行する plain GD は

$$
\theta_{n+m}
=
\theta_B^\star+(I-\eta H_B)^m(\theta_A^\star-\theta_B^\star).
$$

$\rho(I-\eta H_B)<1$ なら

$$
\left\|\theta_{n+m}-\theta_B^\star\right\|
\le
q_B^m\left\|\theta_A^\star-\theta_B^\star\right\|,
\qquad 0<q_B<1.
$$

したがって $m$ が十分なら最終 parameter は Phase 1 optimum より Phase 3 optimum に近づく。$M(\theta_A^\star)>0$、$M(\theta_B^\star)<0$ かつ $M$ が $L_M$-Lipschitz で

$$
q_B^m\left\|\theta_A^\star-\theta_B^\star\right\|
<\frac{|M(\theta_B^\star)|}{L_M}
$$

なら

$$
M(\theta_{n+m})<0
$$

が十分条件になる。

## 7. Momentum SGD

実装の momentum SGD は

$$
v_{k+1}=\mu v_k+\nabla F_{z_k}(\theta_k),
$$

$$
\theta_{k+1}=\theta_k-\eta v_{k+1},
\qquad\mu=0.95.
$$

Phase $B$ の二次近似で $e_k=\theta_k-\theta_B^\star$ とすると

$$
\begin{bmatrix}
e_{k+1}\\v_{k+1}
\end{bmatrix}
=
\underbrace{
\begin{bmatrix}
I-\eta H_B & -\eta\mu I\\
H_B & \mu I
\end{bmatrix}
}_{M_B}
\begin{bmatrix}
e_k\\v_k
\end{bmatrix}.
$$

block schedule は

$$
z_{\mathrm{attack}}=M_B^mM_A^nz_0
$$

であり、random schedule は $M_A,M_B$ の混合積になる。一般に

$$
M_B^mM_A^n\ne\prod_{k=1}^{n+m}M_{z_k}.
$$

momentum が常に後半 sample を機械的に重くするのではない。重要なのは、Phase 3 後に Phase 1 gradient が来ない、有限時間・非可換な update trajectory である。

## 8. 主張の範囲

この profile が支持する理論的主張は次である。

> source label を維持した fixed pool $D=A\cup B$ に対し、$B$ を source-trained selector の high-confidence disagreement set とし、Phase 1 classifier の test-feature kernel と $B$ が負の signed-margin coupling を持つなら、有限回 momentum SGD の $A\rightarrow B$ block schedule は、同じ $D$ の random permutation と異なる終点に到達し、十分な tail contraction があれば test margin を反転させうる。

これは「任意のデータ・任意の LSTM・任意の順序で反転する」という一般定理ではない。特に、負の kernel coupling はデータ依存の仮定であり、この profile では selector-disagreement selection により意図的に作られている。
