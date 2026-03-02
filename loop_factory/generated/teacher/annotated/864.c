int main1(int m,int n){
  int j, l, y, c;

  j=76;
  l=3;
  y=m;
  c=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l <= j;
  loop invariant 3 <= l;
  loop invariant (m == 0) ==> (y == 0);
  loop invariant (m != 0) ==> (y != 0);
  loop invariant (l == 3) ==> (y == m);
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant l >= 3;
  loop invariant j == 76;

  loop invariant (\at(m,Pre) >= 0) ==> (y >= 0);
  loop invariant (\at(n,Pre) >= 0) ==> (c >= 0);
  loop invariant m == \at(m, Pre) && l <= j && (l == 3 ==> y == m && c == n);
  loop invariant n == \at(n, Pre) && l >= 3;
  loop invariant l >= 3 && j == 76;

  loop invariant l >= 3 && l <= j && m == \at(m, Pre) && n == \at(n, Pre);
  loop invariant (m >= 0) ==> (y >= 0) && (m <= 0) ==> (y <= 0);
  loop assigns l, y, c;
*/
while (l<j) {
      y = y*2;
      c = c/2;
      l = l+1;
  }

}
