int main1(int k,int p){
  int v, r, u;

  v=k-4;
  r=0;
  u=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == k - 4;
  loop invariant 0 <= r;

  loop invariant 2*(u - k) == r*(r - 1);
  loop invariant u == \at(k, Pre) + r*(r-1)/2;
  loop invariant v == \at(k, Pre) - 4;
  loop invariant k == \at(k, Pre);
  loop invariant v >= 0 ==> r <= v;
  loop invariant r >= 0;
  loop invariant u == k + r*(r-1)/2;
  loop invariant p == \at(p,Pre);
  loop assigns r, u;
*/
while (r<v) {
      u = r+u;
      r = r+1;
  }

}
