int main1(){
  int l, r, iz, rp;
  l=(1%25)+8;
  r=1;
  iz=r;
  rp=20;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (iz - 1) % 8 == 0;
  loop invariant rp == 20 + ((iz - 1) / 8) * (r + 1);
  loop invariant r == 1;
  loop invariant l == 9;
  loop invariant 0 <= l - iz;
  loop assigns rp, iz;
*/
while (iz<=l-1) {
      rp += r;
      iz += 8;
      rp++;
  }
}