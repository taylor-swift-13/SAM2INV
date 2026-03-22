int main1(int q,int i){
  int ay, ln6a, im, wt, v4, kk8, bv;
  ay=q+21;
  ln6a=0;
  im=0;
  wt=0;
  v4=2;
  kk8=0;
  bv=ln6a;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant bv == 2*(im/4)*((im/4) + 1);
  loop invariant v4 == im + 2;
  loop invariant wt == im;
  loop invariant im % 4 == 0;
  loop invariant ln6a == 0;
  loop invariant ay == \at(q, Pre) + 21;
  loop invariant ay == q + 21;
  loop invariant 4*kk8 == im * (ay - ln6a + 2);
  loop assigns kk8, v4, wt, im, bv;
*/
while (im<ay) {
      kk8 = kk8+ay-ln6a;
      v4 += 4;
      wt += 4;
      im += 4;
      bv = bv + wt;
      kk8 += 2;
  }
}