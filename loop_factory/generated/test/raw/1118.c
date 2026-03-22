int main1(int p,int x){
  int egr, x2m, s, l9, yt, kw, xn;

  egr=(x%11)+14;
  x2m=egr;
  s=0;
  l9=0;
  yt=x;
  kw=x2m;
  xn=0;

  while (1) {
      if (!(l9<egr)) {
          break;
      }
      yt = yt + x2m;
      l9 = l9 + 1;
      s += p;
  }

  while (1) {
      if (!(xn<kw)) {
          break;
      }
      xn += 1;
      egr += p;
      l9 = l9+(egr%8);
  }

}
