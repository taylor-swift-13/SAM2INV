int main1(){
  int mc, k15, hm;
  mc=1*4;
  k15=mc;
  hm=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant hm == (mc*(mc+1))/2 - (k15*(k15+1))/2;
  loop invariant 0 <= k15;
  loop invariant k15 <= mc;
  loop assigns hm, k15;
*/
for (; k15>=1; k15 = k15 - 1) {
      hm = hm + k15;
  }
}