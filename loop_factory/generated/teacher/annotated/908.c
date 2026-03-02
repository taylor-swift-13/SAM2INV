int main1(int b,int n){
  int r, f, v, a;

  r=25;
  f=3;
  v=n;
  a=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@

  loop invariant b == \at(b, Pre) && n == \at(n, Pre);
  loop invariant f >= 3;
  loop invariant r == 25 && f >= 3;
  loop invariant r == 25;
  loop invariant b == \at(b, Pre);
  loop invariant n == \at(n, Pre);

  loop invariant a == 2*v - n;
  loop invariant n == \at(n, Pre) && b == \at(b, Pre) && r == 25 && f >= 3;
  loop invariant a == 2*v - n && f >= 3;
  loop invariant r == 25 && b == \at(b, Pre) && n == \at(n, Pre);
  loop invariant 2*v == a + n;
  loop invariant a == 2*v - \at(n, Pre);
  loop assigns a, v, f;
*/
while (1) {
      v = v*2;
      a = a+v;
      f = f+1;
  }

}
