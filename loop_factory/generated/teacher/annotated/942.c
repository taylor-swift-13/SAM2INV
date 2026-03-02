int main1(int a,int m){
  int l, u, k;

  l=23;
  u=2;
  k=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant k >= a;

  loop invariant l == 23;
  loop invariant a == \at(a, Pre) && k >= a && l == 23;
  loop invariant k >= \at(a,Pre);
  loop invariant a == \at(a,Pre);
  loop invariant m == \at(m,Pre);

  loop invariant a == \at(a, Pre) && m == \at(m, Pre);
  loop invariant k == \at(a, Pre) || k >= 0;

  loop invariant k >= 0 || k == \at(a, Pre);
  loop invariant (k >= a) && (l == 23);
  loop assigns k;
*/
while (1) {
      k = k+2;
      k = k*k;
  }

}
