int main1(int k,int n){
  int m, y, v;

  m=k;
  y=m;
  v=y;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == \at(k, Pre) && y == m;
  loop invariant v >= y && k == \at(k, Pre);
  loop invariant m == \at(k, Pre) && y == m && n == \at(n, Pre);
  loop invariant y == \at(k, Pre) && m == y;
  loop invariant m == \at(k, Pre);
  loop invariant y == \at(k, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant v >= y;
  loop invariant m == \at(k, Pre) && y == \at(k, Pre) && k == \at(k, Pre) && n == \at(n, Pre);
  loop invariant v >= \at(k, Pre) && v >= m;
  loop invariant y == m;
  loop invariant v >= m;
  loop invariant v >= \at(k, Pre);
  loop invariant k == \at(k, Pre) && n == \at(n, Pre);
  loop invariant m == \at(k, Pre) && y == \at(k, Pre) && k == \at(k, Pre);
  loop invariant n == \at(n, Pre) && (y >= 1 ==> v >= \at(k, Pre));
  loop invariant v == \at(k, Pre) || v >= \at(k, Pre) + 4;
  loop assigns v;
*/
while (y>=1) {
      v = v+4;
      if (y<v+2) {
          v = v+v;
      }
      if (y+7<=v+m) {
          v = v+y;
      }
  }


  int __aux_loop = 0;
  while (__aux_loop < 2) {
      __aux_loop = __aux_loop + 1;
  }
/*@
  assert !(__aux_loop < 2) &&
         (m == \at(k, Pre) && y == m);
*/

}
