int main1(int b,int k){
  int a, s, c, n;

  a=80;
  s=0;
  c=-17823;
  n=2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 4*(c + 17823) == (n - 2)*(n - 2);
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant a == 80;
  loop invariant n >= 2;
  loop invariant n % 2 == 0;
  loop invariant c == -17823 + ((n - 2)/2) * ((n - 2)/2);
  loop invariant ((n - 2) % 2) == 0;
  loop invariant c >= -17823;
  loop invariant 4*c - (n - 2) * (n - 2) == -71292;
  loop invariant 4*(c + 17823) == (n - 2) * (n - 2) && a == 80;
  loop invariant b == \at(b, Pre) && k == \at(k, Pre) && n >= 2 && n % 2 == 0;
  loop invariant n % 2 == 0 ==> c == -17823 + ((n - 2) / 2) * ((n - 2) / 2);
  loop assigns c, n;
*/
while (c<=-3) {
      c = c+n-1;
      n = n+2;
  }
/*@
  assert !(c<=-3) &&
         (4*(c + 17823) == (n - 2)*(n - 2));
*/


}
