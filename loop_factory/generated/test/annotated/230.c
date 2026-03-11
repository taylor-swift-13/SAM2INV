int main1(){
  int sxl8, vf1, nf2, al4, s1, c4;
  sxl8=60;
  vf1=sxl8+3;
  nf2=0;
  al4=0;
  s1=sxl8;
  c4=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant nf2 == al4;
  loop invariant s1 == sxl8 + (al4*(al4+1))/2 + al4*c4;
  loop invariant c4 == 0;
  loop invariant (0 <= al4 && al4 <= sxl8);
  loop assigns al4, nf2, s1;
*/
while (al4<=sxl8-1) {
      al4 += 1;
      nf2++;
      s1 += nf2;
      s1 = s1 + c4;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= c4;
  loop invariant c4 <= al4;
  loop invariant vf1 == (sxl8 + 3) + (c4*(c4-1))/2;
  loop invariant nf2 >= sxl8;
  loop assigns nf2, vf1, c4;
*/
while (1) {
      nf2 = nf2 + vf1;
      vf1 = vf1 + c4;
      c4++;
      if (c4>=al4) {
          break;
      }
  }
}