int main1(int k,int n){
  int f, i, m;

  f=78;
  i=0;
  m=1;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == 0;
  loop invariant f == 78;
  loop invariant 2 <= f;
  loop invariant m % 2 == 1;
  loop invariant k == \at(k, Pre) && n == \at(n, Pre);
  loop invariant i == 0 && f == 78 && i <= f && m >= 1;
  loop invariant i <= f;
  loop invariant m >= 1;
  loop invariant k == \at(k, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant 0 <= i && i <= f;
  loop invariant n == \at(n, Pre) && k == \at(k, Pre);
  loop invariant f == 78 && i == 0 && m >= 1 && (m - 1) % 2 == 0;
  loop invariant f >= 2 && n == \at(n, Pre) && k == \at(k, Pre);
  loop invariant f >= 2;
  loop assigns m;
*/
while (i<=f-1) {
      m = m+2;
      if (i+2<=i+f) {
          m = m+i;
      }
      else {
          m = m+1;
      }
  }

}
