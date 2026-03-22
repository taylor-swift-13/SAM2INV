int main1(int t,int p){
  int g, wz, l60k, l, o;

  g=18;
  wz=0;
  l60k=10;
  l=1;
  o=0;

  while (1) {
      if (!(l60k>0&&l<=g)) {
          break;
      }
      if (l60k>l) {
          l60k -= l;
      }
      else {
          l60k = 0;
      }
      l = l + 1;
      wz++;
      o = o + 1;
  }

}
