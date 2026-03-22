int main1(int o){
  int f, p, k, m, mw, fw;
  f=o;
  p=1;
  k=0;
  m=1;
  mw=1;
  fw=p;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant fw == m;
  loop invariant m == (k + 1) * (k + 1);
  loop invariant mw == 2 * k + 1;
  loop invariant f == \at(o, Pre);
  loop invariant k >= 0;
  loop assigns k, mw, m, fw;
*/
while (m<=f) {
      k += 1;
      mw += 2;
      m += mw;
      fw += mw;
  }
}