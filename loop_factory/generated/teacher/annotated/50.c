int main1(int b,int m){
  int l, s, k, v;

  l=52;
  s=0;
  k=-8;
  v=-6;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k + 11*s == -8 && l == 52 && v == -6 && m == \at(m, Pre) && b == \at(b, Pre);
  loop invariant s <= l;
  loop invariant k == -8 + s*(2*v + 1);
  loop invariant 0 <= s;
  loop invariant v == -6;
  loop invariant l == 52;
  loop invariant b == \at(b, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant k == -8 - 11*s;
  loop invariant k + 11*s == -8;
  loop invariant s >= 0;
  loop assigns k, s;
*/
while (s<l) {
      k = k+v+v;
      k = k+1;
      s = s+1;
  }

}
