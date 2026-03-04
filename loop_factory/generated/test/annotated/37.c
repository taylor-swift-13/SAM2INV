int main1(){
  int dn;
  dn=(1%20)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant dn >= 0;
  loop invariant dn == 0 || dn >= 5;
  loop invariant dn != 1;
  loop invariant dn != 2;
  loop invariant dn != 3;
  loop invariant dn != 4;
  loop invariant dn >= (1%20) + 5;
  loop invariant dn != -1;
  loop invariant dn <= (dn - 1) * (dn - 1);
  loop invariant dn >= 6;
  loop invariant dn > 0;
  loop assigns dn;
*/
while (dn>0) {
      dn--;
      dn = dn*dn;
  }
}