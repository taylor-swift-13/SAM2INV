int main1(){
  int k, rh;
  k=1+14;
  rh=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == 1 + 14;
  loop invariant rh <= k;
  loop invariant rh >= 2;
  loop assigns rh;
*/
while (1) {
      rh += 1;
      if (rh>=k) {
          break;
      }
  }
}