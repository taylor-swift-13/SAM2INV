int main1(int p,int x){
  int egr, x2m, s, l9, yt, kw, xn;
  egr=(x%11)+14;
  x2m=egr;
  s=0;
  l9=0;
  yt=x;
  kw=x2m;
  xn=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant yt == \at(x, Pre) + l9 * x2m;
  loop invariant s == p * l9;
  loop invariant egr == x2m;
  loop invariant egr == ((\at(x, Pre) % 11) + 14);
  loop invariant 0 <= l9 <= egr;
  loop invariant yt == x + l9 * x2m;
  loop assigns yt, l9, s;
*/
while (1) {
      if (!(l9<egr)) {
          break;
      }
      yt = yt + x2m;
      l9 = l9 + 1;
      s += p;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant egr == kw + xn * p;
  loop invariant kw == ((\at(x, Pre) % 11) + 14);
  loop invariant 0 <= xn <= kw;
  loop assigns xn, egr, l9;
*/
while (1) {
      if (!(xn<kw)) {
          break;
      }
      xn += 1;
      egr += p;
      l9 = l9+(egr%8);
  }
}