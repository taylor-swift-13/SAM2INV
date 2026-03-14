int main1(){
  int g3, c3b1, ci, e;
  g3=1;
  c3b1=5;
  ci=0;
  e=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e == ci*(ci+1)/2;
  loop invariant 0 <= ci;
  loop invariant (g3 == 1) || (g3 == c3b1 + 5);
  loop invariant c3b1 == 5;
  loop invariant g3 <= c3b1 + 5;
  loop assigns ci, e, g3;
*/
while (c3b1+6<=g3) {
      ci = ci + 1;
      e += ci;
      g3 = (c3b1+6)-1;
  }
}