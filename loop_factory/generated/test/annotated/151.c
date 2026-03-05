int main1(){
  int v4, zt54;
  v4=1+25;
  zt54=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v4 == 26;
  loop invariant zt54 >= 0;
  loop invariant zt54 % (v4 + 1) == 0;
  loop assigns zt54;
*/
while (1) {
      if (zt54<=zt54*zt54+zt54) {
          break;
      }
      if (zt54==zt54-1) {
          zt54 = 0;
          zt54++;
      }
      else {
          zt54++;
      }
      zt54 += v4;
  }
}