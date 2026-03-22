int main1(){
  int q, tcg, um0, sk;
  q=1+12;
  tcg=(1%40)+2;
  um0=0;
  sk=20;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant sk >= 20;
  loop invariant tcg * um0 <= q;
  loop invariant tcg == 3;
  loop invariant 0 <= um0 <= 3;
  loop assigns sk, tcg, um0;
*/
while (tcg!=um0) {
      um0 = tcg;
      tcg = (tcg+q/tcg)/2;
      sk += tcg;
  }
}