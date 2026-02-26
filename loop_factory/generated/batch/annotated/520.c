int main1(int a,int k){
  int l, j, r, v;

  l=23;
  j=0;
  r=k;
  v=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r - k == 3*(v - l);
  loop invariant v >= l;
  loop invariant j <= l;
  loop invariant a == \at(a, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant l == 23;
  loop invariant j == 0;
  loop invariant r >= k;
  loop invariant 3*v - r == 3*l - k;
  loop invariant r - 3*v == k - 3*l;
  loop invariant j >= 0;
  loop invariant r - 3*v == \at(k, Pre) - 69;
  loop invariant r >= \at(k, Pre);
  loop invariant v >= 23;
  loop assigns r, v;
*/
while (j<l) {
      r = r+2;
      v = v+2;
      r = r+1;
      v = v-1;
  }

}
