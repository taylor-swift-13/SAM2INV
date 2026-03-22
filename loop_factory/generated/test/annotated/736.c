int main1(int d,int h){
  int yz, q6o, dt, gn;
  yz=(d%29)+16;
  q6o=0;
  dt=(d%28)+10;
  gn=-4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant gn == -4 + yz * q6o;
  loop invariant dt == (\at(d,Pre) % 28) + 10 - (q6o * (q6o - 1)) / 2;
  loop invariant d == \at(d, Pre);
  loop invariant h == \at(h, Pre);
  loop invariant q6o >= 0;
  loop assigns dt, q6o, gn;
*/
while (dt>q6o) {
      dt -= q6o;
      q6o = (1)+(q6o);
      gn = gn + yz;
  }
}