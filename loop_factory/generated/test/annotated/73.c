int main1(int u){
  int bw3s, e, d, ae, vx;
  bw3s=u;
  e=0;
  d=e;
  ae=u;
  vx=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant bw3s == \at(u, Pre);
  loop invariant ae + d == u;
  loop invariant (e == 0) || (e == bw3s);
  loop invariant bw3s == u;
  loop assigns ae, d, e, vx;
*/
while (e<bw3s) {
      ae -= 4;
      d += 4;
      vx = (d)+(vx);
      e = bw3s;
  }
}