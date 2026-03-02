int main1(int a,int k){
  int l, r, m;

  l=k;
  r=0;
  m=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r == 0;
  loop invariant l == \at(k, Pre);
  loop invariant m >= \at(k, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant a == \at(a, Pre);
  loop invariant r % 5 == 0;
  loop invariant l == k;
  loop invariant m >= k;
  loop invariant r == 0 && l == k;
  loop invariant m >= k && m >= l;
  loop invariant m >= l;
  loop invariant a == \at(a, Pre) && k == \at(k, Pre);
  loop invariant a == \at(a,Pre);
  loop invariant k == \at(k,Pre);
  loop assigns m;
*/
while (1) {
      m = m+2;
      if ((r%5)==0) {
          m = m*m;
      }
      else {
          m = m*m+m;
      }
  }

}
