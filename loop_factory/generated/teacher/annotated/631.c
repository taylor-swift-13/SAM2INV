int main1(int k,int m){
  int l, f, v, c, s, e;

  l=(k%18)+15;
  f=l;
  v=k;
  c=m;
  s=f;
  e=-3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f == l;
  loop invariant l == (k % 18) + 15;
  loop invariant v - k == f - l;
  loop invariant c - m == s * (f - l);
  loop invariant s == l;
  loop invariant f - v == l - k;
  loop invariant f <= l;
  loop invariant c - s*(f - l) == m;
  loop invariant c - s*v == m - s*k;
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant c - m == (f - l) * s;
  loop invariant l == (\at(k, Pre) % 18) + 15;
  loop invariant c == m + (f - l) * s;
  loop assigns v, f, c;
*/
while (1) {
      if (f>=l) {
          break;
      }
      v = v+1;
      f = f+1;
      c = c+s;
  }

}
