int main1(int c,int x){
  int mlw, zwx, yz, fru;

  mlw=35;
  zwx=mlw;
  yz=3;
  fru=0;

  while (zwx<mlw) {
      fru = zwx%5;
      if (zwx>=yz) {
          yz = (zwx-yz)%5;
          yz = yz+fru-yz;
      }
      else {
          yz = yz + fru;
      }
      x = x + fru;
      zwx++;
  }

}
