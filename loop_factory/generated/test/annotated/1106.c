int main1(int k){
  int i0, f, ra, nb, v5, b, yk;
  i0=k;
  f=0;
  ra=0;
  nb=0;
  v5=0;
  b=0;
  yk=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant yk + b + v5 + nb == ra;
  loop invariant k >= \at(k, Pre);
  loop invariant i0 == \at(k, Pre);
  loop invariant nb >= 0;
  loop invariant b >= 0;
  loop invariant v5 >= 0;
  loop invariant yk >= 0;
  loop assigns ra, k, yk, b, v5, nb;
*/
while (1) {
      if (!(ra<=i0-1)) {
          break;
      }
      if (ra%11==0) {
          yk = yk + 1;
      }
      else {
          if (ra%5==0) {
              b += 1;
          }
          else {
              if (ra%6==0) {
                  v5 = v5 + 1;
              }
              else {
                  nb++;
              }
          }
      }
      ra++;
      k += nb;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k >= \at(k, Pre);
  loop invariant nb >= 0;
  loop invariant ra >= 0;
  loop invariant b >= 0;
  loop assigns ra, i0, b, k;
*/
while (b<f) {
      ra += b;
      i0 = i0+f-nb;
      b += 1;
      k += b;
  }
}