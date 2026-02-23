int main1(int m){
  int l, r, j;

  l=47;
  r=l;
  j=-4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == 47;
  loop invariant m == \at(m, Pre);
  loop invariant 0 <= r;
  loop invariant r <= 47;
  loop invariant r % 4 == 3;
  loop invariant r <= l;
  loop invariant r >= 3;
  loop invariant (l - r) % 4 == 0;
  loop invariant (r % 4) == 3;
  loop invariant r % 4 == l % 4;
  loop assigns r;
*/
while (r-4>=0) {
      r = r-4;
  }

}
