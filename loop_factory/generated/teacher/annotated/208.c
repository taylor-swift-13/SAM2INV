int main1(int k,int p){
  int g, l, m, v;

  g=54;
  l=g;
  m=l;
  v=g;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m <= g + 1;
  loop invariant ((m - g) % 2 == 0);
  loop invariant k == \at(k, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant m >= 54;
  loop invariant g == 54;
  loop invariant (m - g) % 2 == 0;
  loop invariant (g - m) % 2 == 0;
  loop invariant m <= g;
  loop invariant m % 2 == 0;
  loop assigns m;
*/
while (m<g) {
      if (m<g) {
          m = m+1;
      }
      m = m+1;
  }

}
