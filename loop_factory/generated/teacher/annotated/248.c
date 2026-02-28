int main1(int n,int p){
  int k, f, h, o;

  k=27;
  f=k;
  h=k;
  o=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f == 27;
  loop invariant k == 27;
  loop invariant n == \at(n, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant o > 0;
  loop invariant h >= k;
  loop invariant h <= k + o;
  loop invariant h - k <= o;
  loop invariant o >= 27;
  loop invariant o % 27 == 0;
  loop invariant h <= o;
  loop invariant f == k;

  loop invariant f >= 3;
  loop assigns h, o;
*/
while (f-3>=0) {
      if (h+5<=k) {
          h = h+5;
      }
      else {
          h = k;
      }
      h = h+o;
      o = o+o;
  }

}
