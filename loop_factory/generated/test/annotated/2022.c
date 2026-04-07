int main1(){
  int nz, te, a, zpr, k30;
  nz=1*3;
  te=0;
  a=0;
  zpr=-8;
  k30=te;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == te;
  loop invariant zpr == -8 + 2*te;
  loop invariant k30 == (te*(te+1))/2;
  loop invariant (0 <= te && te <= nz);
  loop assigns a, te, zpr, k30;
*/
while (1) {
      if (!(te < nz)) {
          break;
      }
      a = (1)+(a);
      te++;
      zpr += 2;
      k30 = k30 + te;
  }
}