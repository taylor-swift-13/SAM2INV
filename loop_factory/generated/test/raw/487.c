int main1(){
  int r, d, f, ag7, cz8, j1n, kn58;

  r=54;
  d=r+6;
  f=0;
  ag7=0;
  cz8=0;
  j1n=(1%18)+5;
  kn58=d;

  while (j1n>=1) {
      cz8 = cz8+1*1;
      f = f+1*1;
      ag7 = ag7+1*1;
      j1n -= 1;
      kn58 = kn58*4+(ag7%5)+0;
  }

  while (ag7>d) {
      ag7 -= d;
      d++;
      f = (d)+(f);
      f = f%5;
  }

}
