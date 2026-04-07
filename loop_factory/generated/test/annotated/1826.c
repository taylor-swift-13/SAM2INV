int main1(){
  int tqk, d9xs, v0, gj, giw, i6, wk;
  tqk=72;
  d9xs=0;
  v0=0;
  gj=d9xs;
  giw=tqk;
  i6=1+1;
  wk=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant wk >= 0;
  loop invariant i6 >= 2;
  loop invariant d9xs <= tqk;
  loop invariant v0 == 0;
  loop invariant gj == 0;
  loop invariant giw == 72;
  loop invariant 0 <= d9xs;
  loop invariant tqk == 72;
  loop invariant wk <= i6;
  loop assigns d9xs, wk, i6, v0;
*/
while (1) {
      if (!(d9xs < tqk)) {
          break;
      }
      d9xs = d9xs + 1, wk = wk + v0*v0 + gj*gj + i6*giw;
      i6 = i6 + 1;
      i6 = i6*i6+v0;
      wk = i6+(-5);
      v0 = v0%9;
  }
}