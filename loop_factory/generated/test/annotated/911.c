int main1(int c,int i){
  int lkr0, cfz, ht3c, p, b;
  lkr0=c+16;
  cfz=0;
  ht3c=1;
  p=0;
  b=lkr0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c == \at(c, Pre) + 2 * (ht3c - 1);
  loop invariant b == lkr0 * ht3c;
  loop invariant p*6 == (ht3c - 1) * ht3c * (2*ht3c - 1);
  loop invariant cfz == 0;
  loop invariant i == \at(i,Pre);
  loop assigns p, b, c, ht3c;
*/
while (ht3c<=lkr0) {
      p = p+ht3c*ht3c;
      b = b+lkr0-cfz;
      c += 2;
      ht3c++;
  }
}