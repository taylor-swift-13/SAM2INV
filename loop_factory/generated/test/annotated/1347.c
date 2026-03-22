int main1(){
  int w, k, s2, y0;
  w=0;
  k=0;
  s2=(1%28)+10;
  y0=w;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s2 + k*(k-1)/2 == 11;
  loop invariant y0 == 11*k - k*(k+1)*(k-1)/6;
  loop invariant s2 == 11 - k*(k-1)/2 && k >= 0;
  loop invariant y0 == 11*k - k*(k-1)*(k+1)/6 && w == 0;
  loop invariant 2*s2 + k*(k-1) == 22;
  loop invariant s2 <= 11;
  loop invariant k >= 0;
  loop invariant y0 == k * s2 + k * (k - 1) * (2 * k - 1) / 6;
  loop invariant s2 >= 0;
  loop assigns s2, y0, k;
*/
while (s2>k) {
      s2 = s2 - k;
      y0 = y0 + s2;
      k += 1;
  }
}