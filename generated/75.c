int main75(int c,int n,int b){
  int ldy, yw65, h4c, lbjq, y, w;

  ldy=(c%16)+17;
  yw65=ldy;
  h4c=(c%20)+10;
  lbjq=(c%15)+8;
  y=6;
  w=-1;

  while (h4c>0&&lbjq>0) {
      if (yw65%2==0) {
          h4c--;
      }
      else {
          lbjq = lbjq - 1;
      }
      yw65 += 1;
      c = c+(yw65%2);
      y = y+(yw65%2);
      w = w+(h4c%8);
  }

}
