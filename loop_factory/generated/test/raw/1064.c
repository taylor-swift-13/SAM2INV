int main1(){
  int yp, fxf, yb, soe;

  yp=0;
  fxf=(1%18)+5;
  yb=(1%15)+3;
  soe=fxf;

  while (1) {
      if (!(fxf!=0)) {
          break;
      }
      yb--;
      soe = soe + yp;
      fxf--;
  }

  while (fxf-2>=0) {
      yp = yp+yb*fxf;
      fxf = fxf + 1;
  }

}
