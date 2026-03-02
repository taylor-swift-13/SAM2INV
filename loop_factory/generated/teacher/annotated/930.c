int main1(int b,int n){
  int d, i, t, p;

  d=10;
  i=d;
  t=-2;
  p=i;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i <= d;
  loop invariant i >= 0;
  loop invariant d == 10;
  loop invariant b == \at(b, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant b == \at(b, Pre) && n == \at(n, Pre) && i >= 0 && i <= 10;
  loop invariant i >= 0 && i <= d;
  loop invariant b == \at(b, Pre) && n == \at(n, Pre);
  loop assigns i;
*/
while (i>=1) {
      i = i/2;
  }

}
