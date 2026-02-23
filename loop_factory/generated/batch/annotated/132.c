int main1(int q){
  int x, p, s, g;

  x=q+17;
  p=0;
  s=x;
  g=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p == 0;
  loop invariant x == q + 17;
  loop invariant (s == x) || (s == x+1);
  loop invariant x == \at(q, Pre) + 17;
  loop invariant q == \at(q, Pre);
  loop invariant s == x || s == x + 1;
  loop invariant x <= s;
  loop invariant s <= x + 1;
  loop invariant s >= x;
  loop assigns s;
*/
while (p+2<=x) {
      if (s+3<=x) {
          s = s+3;
      }
      else {
          s = x;
      }
      s = s+1;
  }

}
