int main1(){
  int a, go, lzk, t, djs, wnxc;

  a=60;
  go=3;
  lzk=-3;
  t=0;
  djs=go;
  wnxc=a;

  while (1) {
      if (!(lzk<=a-1)) {
          break;
      }
      t = t + lzk;
      lzk++;
      djs = djs + 1;
      wnxc += t;
  }

}
