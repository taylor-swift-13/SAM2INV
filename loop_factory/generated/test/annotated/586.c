int main1(int e,int g){
  int i, u, s2e, zot, rnp;
  i=14;
  u=i;
  s2e=0;
  zot=0;
  rnp=u;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (i == 14);
  loop invariant (0 <= s2e <= i);
  loop invariant (s2e % 2 == 0);
  loop invariant zot == 0;
  loop invariant rnp == 14 + (s2e/2) * ((s2e/2) + 1);
  loop invariant 4*(rnp - i) == s2e*(s2e + 2);
  loop assigns s2e, zot, rnp;
*/
while (1) {
      if (!(s2e<i)) {
          break;
      }
      s2e += 2;
      if (!(!(rnp<=zot))) {
          zot = rnp;
      }
      rnp += s2e;
  }
}