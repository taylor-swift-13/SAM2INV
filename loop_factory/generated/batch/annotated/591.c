int main1(int m,int n){
  int k, g, h;

  k=78;
  g=0;
  h=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g == 0;
  loop invariant k == 78;
  loop invariant h >= n;
  loop invariant (h - n) % 2 == 0;
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant ((h - n) % 2) == 0;
  loop invariant h >= \at(n, Pre);
  loop invariant ((h - \at(n, Pre)) % 2 == 0);
  loop invariant ((h - \at(n, Pre)) % 2) == 0;
  loop assigns h;
*/
while (1) {
      h = h+2;
      h = h+g;
  }

}
