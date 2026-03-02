int main1(int m,int n){
  int o, x, d, c;

  o=n+25;
  x=0;
  d=o;
  c=o;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d == o;
  loop invariant o == \at(n, Pre) + 25;
  loop invariant x >= 0;
  loop invariant m == \at(m, Pre);
  loop invariant d == \at(n, Pre) + 25;
  loop invariant d == o && o == \at(n, Pre) + 25 && x >= 0;
  loop invariant n == \at(n, Pre);
  loop invariant (c - d) % 2 == 0;

  loop invariant o == 0 ==> c == 0;
  loop invariant x == 0 ==> c == o;
  loop invariant m == \at(m, Pre) && n == \at(n, Pre) && d == o && o == \at(n, Pre) + 25 && x >= 0;
  loop invariant c == o || x > 0;
  loop invariant x >= 0 && o == \at(n, Pre) + 25 && n == \at(n, Pre) && m == \at(m, Pre);
  loop assigns c, x;
*/
while (1) {
      c = c+c;
      c = c+d;
      x = x+1;
  }

}
