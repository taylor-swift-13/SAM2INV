int main1(){
  int dxcq, n, y, tz, mf;

  dxcq=1+16;
  n=0;
  y=(1%40)+2;
  tz=0;
  mf=n;

  while (y!=tz) {
      tz = y;
      y = (y+dxcq/y)/2;
      mf = (mf+tz)+(-(y));
  }

}
