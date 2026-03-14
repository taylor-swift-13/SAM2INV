int main1(int f,int c){
  int rqd, bb, k, kn0, qt;
  rqd=38;
  bb=0;
  k=0;
  kn0=0;
  qt=12;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant qt >= 12;
  loop invariant bb == 0;
  loop invariant k == kn0 * \at(f,Pre) + 19 * kn0 * (kn0 - 1);
  loop invariant 0 <= kn0 <= 38;
  loop invariant k == kn0 * \at(f,Pre) + (kn0 * (kn0 - 1) / 2) * (rqd - bb);
  loop invariant 0 <= kn0 <= rqd;
  loop invariant f == (\at(f, Pre) + kn0 * (rqd - bb));
  loop assigns k, kn0, qt, f;
*/
while (1) {
      if (!(kn0<rqd)) {
          break;
      }
      k += f;
      kn0++;
      qt = qt*2;
      f = f+rqd-bb;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant kn0 == rqd;
  loop invariant bb == 0;
  loop invariant kn0 == 38;
  loop invariant 0 <= qt;
  loop assigns k, f, qt;
*/
while (qt<kn0) {
      qt++;
      k += f;
      f = f+kn0-bb;
      f += bb;
  }
}