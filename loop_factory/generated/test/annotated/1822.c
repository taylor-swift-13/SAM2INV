int main1(){
  int ckb, t, d, w7, u7, m;
  ckb=8;
  t=ckb;
  d=ckb;
  w7=-4;
  u7=(1%35)+8;
  m=1*3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ckb == 8;
  loop invariant w7 >= -4;
  loop invariant m >= 3;
  loop invariant u7 >= 0;
  loop invariant d - w7 == 12;
  loop invariant t >= ckb;
  loop assigns t, w7, d, m, u7;
*/
while (u7>0) {
      t = t+d*d;
      w7 = w7+u7*u7;
      d = d+u7*u7;
      m = m+d+d;
      u7 -= 1;
  }
}