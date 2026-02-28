int main1(int m,int q){
  int x, h, n;

  x=m+10;
  h=0;
  n=h;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x == m + 10;
  loop invariant m == \at(m, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant h >= 0;
  loop invariant n >= 12*h;
  loop invariant n % 12 == 0;
  loop invariant n >= 6*h;
  loop invariant n % 2 == 0;
  loop invariant ((n - 12*h) % 2) == 0;
  loop assigns h, n;
*/
while (1) {
      n = n+6;
      n = n+n;
      h = h+1;
  }

}
