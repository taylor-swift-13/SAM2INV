int main1(int d){
  int x, a, g9og, wokz, fq;

  x=27;
  a=(d%60)+60;
  g9og=(d%9)+2;
  wokz=0;
  fq=0;

  while (1) {
      if (!(a>g9og*wokz+fq)) {
          break;
      }
      if (fq==g9og-1) {
          fq = 0;
          wokz = wokz + 1;
      }
      else {
          fq += 1;
      }
      d += x;
  }

}
