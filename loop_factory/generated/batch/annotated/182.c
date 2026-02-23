int main1(int b,int m){
  int k, j, p, d, w;

  k=14;
  j=k;
  p=-8;
  d=b;
  w=-2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 4*d == 4*b + (p + 8) * (p - 6);
  loop invariant p <= k;
  loop invariant b == \at(b, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant d == \at(b, Pre) + ((p + 8)/2) * (((p + 8)/2) - 7) &&
                     p >= -8 &&
                     ((p + 8) % 2) == 0 &&
                     p <= k;
  loop invariant k == 14;
  loop invariant p >= -8;
  loop invariant 4*d - p*p - 2*p == 4*\at(b, Pre) - 48;
  loop invariant p <= k + 1;
  loop invariant 4*d == p*p + 2*p + 4*\at(b, Pre) - 48;
  loop invariant (p % 2) == 0;
  loop assigns p, d;
*/
while (p<k) {
      if (p<k) {
          p = p+1;
      }
      p = p+1;
      d = d+p;
  }

}
