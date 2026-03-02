int main1(int a,int k){
  int l, r, m;

  l=k;
  r=0;
  m=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r == 0 && l == \at(k, Pre) && k == \at(k, Pre) && a == \at(a, Pre) && m >= \at(k, Pre);

  loop invariant l == \at(k, Pre);
  loop invariant r == 0;

  loop invariant k == \at(k, Pre);
  loop invariant m >= l;
  loop invariant m >= \at(k, Pre);
  loop invariant (m - \at(k, Pre)) % 2 == 0;
  loop invariant m >= \at(k, Pre) && r == 0;
  loop invariant a == \at(a, Pre);
  loop invariant r == 0 && l == \at(k, Pre) && k == \at(k, Pre) && a == \at(a, Pre);

  loop invariant m >= \at(k, Pre) && ((m - \at(k, Pre)) % 2 == 0) && r == 0;
  loop invariant l == \at(k, Pre) && k == \at(k, Pre) && a == \at(a, Pre) && (r % 5) == 0;
  loop assigns m;
*/
while (1) {
      m = m+2;
      if ((r%5)==0) {
          m = m+r;
      }
      else {
          m = m-m;
      }
  }

}
