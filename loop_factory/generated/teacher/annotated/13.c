int main1(int p,int q){
  int c, x, l;

  c=p+10;
  x=0;
  l=3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x >= 0;

  loop invariant c == p + 10;
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant 0 <= x;
  loop invariant l >= 3;
  loop invariant l <= x + 3;
  loop invariant (q + 3 <= 0) ==> (l == 3);

  loop invariant (x <= q+3) ==> (l == 3 + x);

  loop invariant (q <= -3 && l == 3) ||
                   (q > -3 && ((x <= q+3 && l == 3 + x) || (x >= q+3 && l == q + 6)));
  loop invariant 3 <= l;
  loop invariant l - 3 <= x;
  loop assigns x, l;
*/
while (x<c) {
      if (x<q+3) {
          l = l+1;
      }
      x = x+1;
  }

}
