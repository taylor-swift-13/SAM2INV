int main1(){
  int xkx, kc, z30, w1, m2, th, tf, ror1;
  xkx=1*5;
  kc=0;
  z30=17;
  w1=15;
  m2=0;
  th=-6;
  tf=xkx;
  ror1=xkx;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= kc <= xkx;
  loop invariant (th % 2) == 0;
  loop invariant m2 == 0;
  loop invariant z30 == 17 - kc;
  loop invariant w1 == 15 + kc;
  loop invariant xkx == 5;
  loop invariant ror1 >= 0;
  loop assigns z30, w1, m2, kc, ror1, th, tf;
*/
while (1) {
      if (!(kc<=xkx-1)) {
          break;
      }
      if (!(m2!=0)) {
          z30 = z30 - 1;
          w1 = w1 + 1;
          m2 = 0;
      }
      else {
          z30 += 1;
          w1--;
          m2 = 1;
      }
      kc += 1;
      if (tf*tf<=xkx+2) {
          ror1 = th*th;
      }
      th = th+(kc%2);
      th = th*2;
      tf += th;
  }
}