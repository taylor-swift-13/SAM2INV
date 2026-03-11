int main1(){
  int ij5, xp5, e, nlh;
  ij5=1*2;
  xp5=ij5;
  e=2;
  nlh=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant xp5 <= ij5;
  loop invariant (e <= 2) ==> (nlh == 1);
  loop invariant (nlh == 1) || (nlh == -1);
  loop invariant (2 <= e && e <= 6);
  loop invariant (e - xp5) <= 0;
  loop invariant ((e - xp5) % 2 == 0);
  loop assigns xp5, e, nlh;
*/
while (xp5<ij5) {
      if (e>=6) {
          nlh = -1;
      }
      if (e<=2) {
          nlh = 1;
      }
      xp5 = xp5 + 1;
      e += nlh;
  }
}