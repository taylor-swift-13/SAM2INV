int main1(){
  int jb, o, pf1t;
  jb=1+5;
  o=3;
  pf1t=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= pf1t <= 2;
  loop invariant 3 <= o <= jb;
  loop invariant jb == 1 + 5;
  loop invariant (o + pf1t) % 2 == 1;
  loop assigns o, pf1t;
*/
for (; o<jb; o = o + 1) {
      pf1t++;
      if (pf1t>=3) {
          pf1t = pf1t - 3;
          pf1t++;
      }
  }
}