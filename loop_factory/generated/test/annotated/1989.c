int main1(int o){
  int t, pf, kx, v57;
  t=o;
  pf=0;
  kx=0;
  v57=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant kx == (t + 1) * pf;
  loop invariant 5 - pf <= v57;
  loop invariant v57 <= 5 + pf;
  loop invariant pf >= 0;
  loop invariant (t >= 0) ==> (pf <= t);
  loop invariant t == \at(o, Pre);
  loop invariant (pf <= t/2) ==> (v57 == 5 + pf);
  loop assigns kx, pf, v57;
*/
while (pf < t) {
      v57 = v57 + (pf < t/2 ? 1 : -1);
      kx += t;
      pf++;
      kx += 1;
  }
}