int main1(){
  int v0a, ms, bl3, y8, to;

  v0a=1;
  ms=0;
  bl3=0;
  y8=5;
  to=-1;

  while (1) {
      if (!(ms<=v0a-1)) {
          break;
      }
      to += 1;
      y8 = y8 + 1;
      if (y8>=4) {
          y8 -= 4;
          bl3 += 1;
      }
      ms += 1;
  }

}
