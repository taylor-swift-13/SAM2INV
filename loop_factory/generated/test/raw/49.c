int main1(int i){
  int zr0a, xsp, es2l, o9a;

  zr0a=(i%21)+19;
  xsp=0;
  es2l=0;
  o9a=8;

  while (1) {
      if (!(xsp<zr0a&&o9a>0)) {
          break;
      }
      xsp += 1;
      es2l = es2l + o9a;
      o9a -= 1;
      i = i + xsp;
  }

}
