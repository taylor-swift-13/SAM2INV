int main2(int i,int w,int v){
  int u9, oy, ydo, zuz, pz;

  u9=(v%35)+8;
  oy=0;
  ydo=(v%20)+5;
  zuz=1;
  pz=2;

  while (ydo>0) {
      ydo = ydo - 1;
      pz = pz+u9-oy;
      v += ydo;
      zuz += ydo;
      w += ydo;
      zuz = zuz + 5;
  }

}
