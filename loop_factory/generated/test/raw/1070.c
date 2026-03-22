int main1(int j,int s){
  int dk, y3, deie, y9, c, yh;

  dk=s-3;
  y3=0;
  deie=0;
  y9=0;
  c=(s%18)+5;
  yh=0;

  while (1) {
      if (!(c>0)) {
          break;
      }
      c--;
      y3 = y3+j*j;
      deie = deie+s*s;
      y9 = y9+j*s;
      s = s*2+(deie%4)+1;
  }

  while (1) {
      if (!(yh+1<=dk)) {
          break;
      }
      yh = yh + 1;
  }

}
