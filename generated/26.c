int main26(int d,int o){
  int f5w, dai, xq, e, ihb;

  f5w=d;
  dai=0;
  xq=-8;
  e=16;
  ihb=6;

  while (1) {
      e = e*e;
      xq += dai;
      ihb = ihb+xq*e;
      dai += 1;
      if (dai>=f5w) {
          break;
      }
  }

}
