int main1(int p,int q){
  int r, k, l, s;

  r=(p%6)+4;
  k=r;
  l=6;
  s=8;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant k == r;
  loop invariant l >= 6;
  loop invariant l <= r + s;
  loop invariant r == (p % 6) + 4;
  loop invariant l <= r + 8;
  loop invariant r == ((\at(p,Pre)) % 6) + 4;
  loop invariant s == 8;
  loop invariant 6 <= l;
  loop invariant l >= 4;
  loop assigns l;
*/
while (k-1>=0) {
      if (l+3<=r) {
          l = l+3;
      }
      else {
          l = r;
      }
      l = l+s;
  }

}
