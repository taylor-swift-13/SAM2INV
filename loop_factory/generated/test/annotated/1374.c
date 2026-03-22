int main1(int n){
  int m, g6, hcu, x5;
  m=n*5;
  g6=m;
  hcu=m;
  x5=m;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == hcu;
  loop invariant (m - g6) % 4 == 0;
  loop invariant g6 <= m;
  loop invariant m == 5 * n;
  loop assigns x5, g6;
*/
for (; g6>=4; g6 -= 4) {
      x5 = x5*x5+hcu;
  }
}