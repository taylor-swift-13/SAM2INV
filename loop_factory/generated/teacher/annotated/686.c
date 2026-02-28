int main1(int b,int k,int n,int p){
  int h, v, j, w, g;

  h=n+6;
  v=3;
  j=k;
  w=-3;
  g=3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == n + 6;
  loop invariant n == \at(n, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant j >= k;
  loop invariant ((j - k) % 2 == 0);
  loop invariant w == -3 + ((j - k)/2) * (k + (j - k)/2);
  loop invariant ( ( (j - k) % 2 ) == 0 );
  loop invariant ( j >= k );

  loop invariant (j - k) % 2 == 0;
  loop invariant h == \at(n, Pre) + 6;
  loop invariant (j - k) >= 0;
  loop invariant ((j - k) % 2) == 0;
  loop invariant j*j - 4*w == k*k + 12;
  loop assigns j, w;
*/
while (1) {
      j = j+1;
      w = w+j;
      j = j+1;
  }

}
