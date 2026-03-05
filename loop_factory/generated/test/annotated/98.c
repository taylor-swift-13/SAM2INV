int main1(int e,int j){
  int ac4, ib, bw, s8;
  ac4=47;
  ib=0;
  bw=0;
  s8=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ac4 == 47;
  loop invariant ib == 0;
  loop invariant j == \at(j, Pre);
  loop invariant e == \at(e, Pre) + (ac4 - ib) * bw;
  loop invariant bw >= 0;
  loop invariant (bw == 0 && s8 == 3) || (bw >= 1 && s8 + bw == ac4 + 1);
  loop assigns bw, e, s8;
*/
while (ib+1<=ac4) {
      s8 = ac4-bw;
      bw++;
      e = e+ac4-ib;
  }
}