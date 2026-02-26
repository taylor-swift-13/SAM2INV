int main1(int m,int n){
  int o, x, d, c;

  o=n+25;
  x=0;
  d=o;
  c=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o == n + 25;
  loop invariant (d - o) % 6 == 0;
  loop invariant c - m == (2 + x) * ((d - o) / 6);
  loop invariant c == m + ((d - o) / 6) * (2 + x);
  loop invariant x == 0;
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant (c - m) % (2 + x) == 0;
  loop invariant c - m <= 2;
  loop invariant d >= o;
  loop invariant c >= m;
  loop invariant d <= o + 5;
  loop invariant c <= m + 2;
  loop invariant d >= o - 1;
  loop invariant (c - m) % 2 == 0;
  loop assigns c, d;
*/
while (d<o) {
      if (d<o) {
          d = d+1;
      }
      d = d+5;
      c = c+2;
      c = c+x;
  }

}
