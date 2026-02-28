int main1(int b,int n){
  int w, s, v, l;

  w=(b%11)+8;
  s=w;
  v=-6;
  l=w;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant w == (b % 11) + 8;
  loop invariant s == w;
  loop invariant w == (\at(b, Pre) % 11) + 8;
  loop invariant -6 <= v;
  loop invariant v <= w + 2;
  loop invariant b == \at(b, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant v >= -6;
  loop assigns v;
*/
while (s-1>=0) {
      if (v+3<=w) {
          v = v+3;
      }
      else {
          v = w;
      }
      v = v+2;
  }

}
