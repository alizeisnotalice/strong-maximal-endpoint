"""Numerical audit of the plateau root used for the lower bound.

Exact mixture law  S_n = Gamma(n,1) + a_n * Bin(n, rho_n),  a_n = mu - sqrt(mu L/n)/2,
rho_n = 1/(1+exp a_n).  Solves E H_w(S_n - q) = 1 for q and reports
C0 = (q - (n mu - d_n)) / L, the O(L) coefficient claimed to be (9-mu)/24 = 0.3217.
Requires numpy + scipy.  See ../lean/report.md section "原稿缺口".
"""
import numpy as np
from scipy.stats import gamma, binom, norm
from scipy.optimize import brentq
from scipy.integrate import quad
from math import log, sqrt, exp
np.seterr(all='ignore')

def solve_mu(): return brentq(lambda x: x-1-exp(-x), 0.5, 3.0, xtol=1e-15)
mu = solve_mu(); g=(mu-1)/8

def zroot(n):
    c=sqrt(mu/n); return brentq(lambda z: norm.sf(z)-c*z, 0.05, 60.0, xtol=1e-15)

def EHw(n,a,q,w,sd=10.0):
    rho=1.0/(1.0+exp(a)); s=sqrt(n*rho*(1-rho))
    lo=max(0,int(np.floor(n*rho-sd*s))); hi=min(n,int(np.ceil(n*rho+sd*s)))
    ks=np.arange(lo,hi+1,dtype=np.float64); pk=binom.pmf(ks,n,rho)
    cnst=(n/(n-1.0))**n
    c=q-a*ks; arg=w+c
    t1=np.where(c<0, gamma.cdf(np.maximum(arg,0),n,scale=1.0),
                        gamma.cdf(np.maximum(arg,0),n,scale=1.0)-gamma.cdf(np.maximum(c,0),n,scale=1.0))
    sf=gamma.sf(np.maximum(arg,0),n,scale=1.0/(1-1.0/n))
    t2=np.exp(-arg/n)*cnst*sf
    return float(np.dot(pk,t1+t2))

print(f"{'n':>8} {'L':>7} {'z_n':>8} {'C0':>10} {'G(q*)-1':>12} {'q0-qs':>9} {'V/nm-1':>9}")
res=[]
for e in [4,5,6,7,8,9]:
    n=10.0**e; L=log(n); w=L/2+log(L)
    a=mu-0.5*sqrt(mu*L/n); rho=1/(1+exp(a))
    M=n*(1+a*rho); V=n*(1+a*a*rho*(1-rho))
    z=zroot(n); d=sqrt(mu*n)*z; qs=n*mu-d
    fs=EHw(n,a,qs,w)-1.0
    step=max(5.0, 3*L)
    q0=brentq(lambda q: EHw(n,a,q,w)-1.0, qs-step, qs+step, xtol=1e-13)
    C0=(q0-qs)/L
    res.append((n,L,z,C0))
    print(f"1e{e:<6d} {L:7.4f} {z:8.5f} {C0:10.6f} {fs:12.4e} {q0-qs:9.4f} {V/(n*mu)-1:9.2e}")
