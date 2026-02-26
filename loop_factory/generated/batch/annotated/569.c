int main1(int b,int p){
  int h, q, v, k;

  h=(p%21)+14;
  q=0;
  v=q;
  k=-5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == (\at(p, Pre) % 21) + 14;
  loop invariant b == \at(b, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant k == -5;
  loop invariant q >= 0;
  loop invariant 0 <= v <= 25;
  loop invariant q >= 0 && (v == 0 || v == 2 || v == k*k);
  loop invariant h == ((\at(p, Pre) % 21) + 14);
  loop invariant v == 0 || v == 2 || v == 25;

  loop assigns v, q;
*/
while (1) {
      v = v*v+v;
      v = v%3;
      if (q+5<=v+h) {
          v = k*k;
      }
      q = q+1;
  }

}
