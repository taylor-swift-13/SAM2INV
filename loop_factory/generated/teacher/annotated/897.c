int main1(int k,int m){
  int h, r, v;

  h=k-2;
  r=h;
  v=r;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r == h;
  loop invariant h == \at(k, Pre) - 2;
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);

  loop invariant r == k - 2;
  loop invariant v >= r;
  loop invariant h == k - 2;
  loop invariant (r > 0) ==> (v > 0);
  loop invariant r == \at(k,Pre) - 2;
  loop invariant h == \at(k,Pre) - 2;
  loop invariant k == \at(k,Pre);
  loop invariant m == \at(m,Pre);
  loop invariant h == k - 2 && r == h;
  loop invariant k == \at(k, Pre) && m == \at(m, Pre) && v >= h;

  loop invariant v >= k - 2;

  loop invariant h == r;
  loop assigns v;
*/
while (r>0) {
      v = v+3;
      v = v*v+v;
  }

}
