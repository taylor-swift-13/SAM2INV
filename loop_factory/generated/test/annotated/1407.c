int main1(){
  int rk, i, px, ulj;
  rk=1+8;
  i=0;
  px=rk;
  ulj=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant px == rk + ulj;
  loop invariant (i == 0) || (i == rk);
  loop invariant 0 <= i;
  loop invariant i <= rk;
  loop invariant (i == 0) ==> (px == rk);
  loop invariant (i > 0) ==> (px == rk + 1);
  loop assigns ulj, px, i;
*/
while (i<rk) {
      ulj++;
      px++;
      i = rk;
  }
}