int main1(int y,int b){
  int nj, sf, l6, jk0, r2m;
  nj=191;
  sf=2;
  l6=0;
  jk0=sf;
  r2m=nj;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r2m == (l6 + 1) * nj - (l6 * (l6 + 1)) / 2;
  loop invariant 0 <= jk0 <= nj;
  loop invariant r2m == 191 + l6 * nj - (l6 * (l6 + 1)) / 2;
  loop invariant l6 > 0 ==> jk0 == nj - l6;
  loop invariant 0 <= l6;
  loop invariant l6 <= nj;
  loop assigns l6, jk0, r2m;
*/
while (l6<nj) {
      l6 = l6 + 1;
      jk0 = nj-l6;
      r2m = r2m + jk0;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= l6 <= nj;
  loop invariant b == \at(b, Pre) + (nj - l6) * (sf - 2);
  loop invariant l6 == nj;
  loop invariant sf <= nj;
  loop invariant (sf >= 2);
  loop invariant (sf >= 3) ==> (jk0 == nj - sf);
  loop assigns sf, jk0, b;
*/
while (sf<nj) {
      sf++;
      jk0 = nj-sf;
      b = b+nj-l6;
  }
}