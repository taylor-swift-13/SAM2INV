int main1(int p){
  int l, k, r, b;

  l=p+7;
  k=l;
  r=l;
  b=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == p + 7;
  loop invariant p == \at(p, Pre);
  loop invariant r >= p + 7;
  loop invariant (r - l) % 3 == 0;
  loop invariant r >= l;
  loop invariant l == \at(p,Pre) + 7;
  loop invariant r >= \at(p,Pre) + 7;
  loop invariant (r - (\at(p,Pre) + 7)) % 3 == 0;
  loop invariant r <= l + 2;
  loop assigns r;
*/
while (r<l) {
      if (r<l) {
          r = r+1;
      }
      r = r+2;
  }

}
