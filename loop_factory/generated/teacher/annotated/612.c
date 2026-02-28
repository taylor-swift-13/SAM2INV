int main1(int a,int m){
  int n, y, v, o, c, e;

  n=(m%21)+18;
  y=3;
  v=n;
  o=a;
  c=-6;
  e=1;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v - 5*y == n - 15;
  loop invariant c - 3*y == -15;
  loop invariant a == \at(a, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant v == (\at(m,Pre) % 21) + 18 + 5*(y - 3);
  loop invariant c == -6 + 3*(y - 3);
  loop invariant n == (\at(m,Pre) % 21) + 18;
  loop invariant y >= 3;
  loop invariant n == (m%21) + 18;
  loop invariant v == n + 5*(y - 3);
  loop invariant v - 5*y == (\at(m,Pre) % 21) + 3;
  loop assigns v, c, y;
*/
while (1) {
      v = v+5;
      c = c+2;
      c = c+1;
      y = y+1;
  }

}
