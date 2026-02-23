int main1(int b,int n){
  int j, a, e, f;

  j=(b%11)+11;
  a=j;
  e=a;
  f=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e + f == ((b % 11) + 11) + n;
  loop invariant a >= 0 && a <= ((b % 11) + 11) && j == ((b % 11) + 11) && f <= n;
  loop invariant a >= 0;
  loop invariant a <= ((b % 11) + 11);
  loop invariant b == \at(b, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant e >= a;
  loop invariant e + a == 2 * j;
  loop invariant f - a == n - j;
  loop invariant a <= j;
  loop invariant j == ((\at(b, Pre)) % 11) + 11;
  loop invariant e == 2*j - a;
  loop invariant f == n - j + a;
  loop invariant a + e == 2 * j;
  loop invariant j == (b % 11) + 11;
  loop assigns a, e, f;
*/
while (a>0) {
      e = e+1;
      f = f-1;
      a = a-1;
  }

}
