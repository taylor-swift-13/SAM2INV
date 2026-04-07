int main1(int l,int w){
  int q1, va, n, a8, by, s, as, jf, vpp;

  q1=w+11;
  va=0;
  n=q1;
  a8=0;
  by=va;
  s=q1;
  as=w;
  jf=0;
  vpp=w;

  while (va < q1) {
      if ((((l + va) % 3) == 0)) {
          s++;
      }
      if ((((l + va) % 3) == 1)) {
          as += 1;
      }
      if ((((l + va) % 3) == 2)) {
          jf++;
      }
      by = (by+as)%3;
      w = w + s;
      n = n + s;
      va += 1;
      a8 = a8 + s;
      a8 += 2;
      n += 1;
      if (vpp+5<q1) {
          a8 = a8 + va;
      }
      n = n + 3;
  }

}
