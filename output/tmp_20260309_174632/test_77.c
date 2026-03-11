int main1(int s,int x){
  int cr2, so, maf, ke, bh;
  cr2=x-5;
  so=0;
  maf=0;
  ke=0;
  bh=x;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant cr2 == \at(x, Pre) - 5;
  loop invariant maf >= 0;
  loop invariant so == 0;
  loop invariant ke == maf*(maf-1)/2;
  loop invariant bh == \at(x, Pre) + 3*maf;
  loop invariant s == \at(s, Pre) + maf*so;
  loop invariant (maf < cr2) ==> (cr2 - maf > 0);
  loop invariant bh == x + 3*maf;
  loop invariant cr2 == x - 5;
  loop assigns ke, s, maf, bh;
*/
while (1) {
      if (!(maf<cr2)) {
          break;
      }
      ke += maf;
      s += so;
      maf += 1;
      bh = bh + 3;
  }
/*@
  assert (cr2 == \at(x, Pre) - 5) &&
         ((x <= 5 ==> (maf == 0 && ke == 0 && bh == x))) &&
         ((x > 5 ==> (maf == x - 5 && ke == (x - 5) * (x - 6) / 2 && bh == x + 3 * (x - 5))));
*/
}
