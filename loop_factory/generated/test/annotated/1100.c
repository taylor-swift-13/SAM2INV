int main1(int s){
  int o, ws, p0, ppk, v, ytwk, lgw, w;
  o=(s%20)+9;
  ws=2;
  p0=5;
  ppk=0;
  v=ws;
  ytwk=151;
  lgw=ytwk;
  w=ws;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p0 >= 5;
  loop invariant ppk == ((p0 - 1) * p0 * (2 * p0 - 1)) / 6 - 30;
  loop invariant v == ws * (p0 - 4);
  loop invariant v == 2*(p0 - 4);
  loop invariant s == \at(s, Pre) + (p0 - 5) * ws;
  loop invariant v == 2*(p0 - 5) + 2;
  loop assigns ppk, s, v, p0;
*/
while (p0<=o) {
      ppk = ppk+p0*p0;
      s += ws;
      v += 2;
      p0++;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant lgw + 4*w == 159;
  loop invariant lgw >= 0;
  loop assigns w, s, lgw;
*/
while (1) {
      if (!(lgw-4>=0)) {
          break;
      }
      w += 1;
      s -= 1;
      lgw -= 4;
  }
}