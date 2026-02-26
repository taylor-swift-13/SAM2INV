int main1(int b,int p){
  int h, q, v, k;

  h=(p%21)+14;
  q=0;
  v=0;
  k=-5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == \at(p, Pre) % 21 + 14;
  loop invariant p == \at(p, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant q == 0;
  loop invariant (k == -5 && v == 0) || (v - k == 1) || (v - k == h + 1 + q);
  loop invariant h == ((\at(p, Pre) % 21) + 14);

  loop invariant h == (p % 21) + 14;

  loop invariant h == (\at(p, Pre) % 21) + 14;
  loop invariant v == 0 || v == 2*h + 1;
  loop invariant v == 0 || v == 1 + 2*h;
  loop assigns k, v;
*/
while (1) {
      k = h-v;
      v = v+1;
      v = v+k+k;
      if (q+5<=v+h) {
          k = k+h;
      }
      else {
          v = v+q;
      }
  }

}
