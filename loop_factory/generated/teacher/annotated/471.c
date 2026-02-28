int main1(int n,int p){
  int k, f, h, o;

  k=27;
  f=0;
  h=k;
  o=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == 27;
  loop invariant n == \at(n, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant f <= k;
  loop invariant h >= k;
  loop invariant o >= k;
  loop invariant f >= 0;
  loop invariant h >= 27;
  loop invariant o >= 27;
  loop invariant h == k + 3*f;
  loop invariant o == k*(1+f) + (3 * f * (f + 1)) / 2;
  loop invariant 0 <= f;
  loop assigns f, h, o;
*/
while (1) {
      if (f>=k) {
          break;
      }
      h = h+2;
      f = f+1;
      h = h+1;
      o = o+h;
      if (o+4<k) {
          h = h+f;
      }
  }

}
