int main1(int t,int d){
  int vw, u, sw, m, mrq;
  vw=143;
  u=-4;
  sw=0;
  m=0;
  mrq=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == sw*(sw - 1)/2;
  loop invariant d == \at(d,Pre) + sw * u;
  loop invariant 0 <= sw <= vw;
  loop invariant u == -4;
  loop invariant vw == 143;
  loop invariant t == \at(t, Pre);
  loop assigns m, d, sw;
*/
while (sw<vw) {
      m += sw;
      d = d + u;
      sw = sw + 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant u <= mrq;
  loop invariant t == \at(t,Pre);
  loop invariant vw == 143;
  loop invariant mrq == 0;
  loop assigns u;
*/
while (1) {
      u = u + 1;
      if (u>=mrq) {
          break;
      }
  }
}