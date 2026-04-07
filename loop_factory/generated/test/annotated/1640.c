int main1(){
  int q, sfv, dj, t2, f2;
  q=41;
  sfv=0;
  dj=10;
  t2=8;
  f2=12;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant sfv + dj == 10;
  loop invariant t2 == 8 + 11*sfv - (sfv*(sfv - 1))/2;
  loop invariant sfv >= 0;
  loop invariant sfv <= q;
  loop invariant f2 == 12 - sfv;
  loop assigns sfv, dj, t2, f2;
*/
while (sfv < q) {
      sfv = (dj = dj - 1, t2 = t2 - 1, f2 = f2 - 1, sfv + 1);
      t2++;
      t2 += f2;
  }
}