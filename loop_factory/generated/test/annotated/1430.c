int main1(){
  int o1, vp, jt;
  o1=0;
  vp=76;
  jt=38;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o1 == 38 - jt;
  loop invariant vp == 38 + jt;
  loop invariant 0 <= jt;
  loop invariant jt <= 38;
  loop assigns o1, vp, jt;
*/
while (1) {
      if (!(jt>0)) {
          break;
      }
      jt--;
      o1++;
      vp = vp - 1;
  }
}