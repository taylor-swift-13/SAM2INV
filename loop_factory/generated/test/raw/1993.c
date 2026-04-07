int main1(){
  int zz, v7b, lj8f, s0w, dw;

  zz=(1%12)+11;
  v7b=0;
  lj8f=v7b;
  s0w=lj8f;
  dw=3;

  while (v7b < zz) {
      v7b++;
      if (lj8f < s0w) {
          s0w = lj8f;
      }
      dw = dw + v7b;
      lj8f += 4;
  }

}
