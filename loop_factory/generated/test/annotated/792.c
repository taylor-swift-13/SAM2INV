int main1(){
  int ens, bxwu, vl;
  ens=62;
  bxwu=ens;
  vl=8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ens == 62;
  loop invariant vl >= 8;
  loop invariant vl % 8 == 0;
  loop invariant bxwu <= ens;
  loop invariant bxwu >= 0;
  loop assigns bxwu, vl;
*/
for (; bxwu>=1; bxwu -= 1) {
      vl = vl*4;
  }
}