int main1(){
  int d, rg, as, r7b, oz, o7v, cer, b;

  d=1;
  rg=0;
  as=8;
  r7b=15;
  oz=0;
  o7v=rg;
  cer=d;
  b=0;

  while (rg<d) {
      if (oz==0) {
          as += 1;
          r7b--;
          oz = 1;
      }
      else {
          as = as - 1;
          r7b = r7b + 1;
          oz = 0;
      }
      rg++;
      if (rg+4<=b+d) {
          o7v = o7v + oz;
      }
      o7v += 4;
      b = b + rg;
      cer += 1;
  }

}
