int main1(int z){
  int q66, o, l7z, a, mf, y, rq6t, sx, g4;

  q66=z+25;
  o=q66;
  l7z=1;
  a=1;
  mf=1;
  y=1;
  rq6t=o;
  sx=0;
  g4=q66;

  while (1) {
      if (!(mf<=q66)) {
          break;
      }
      l7z = l7z*(z/mf);
      if ((mf/2)%2==0) {
          y = 1;
      }
      else {
          y = -1;
      }
      a = a+y*l7z;
      mf++;
      l7z = l7z*(z/mf);
      if (o+1<=l7z+q66) {
          g4 = z+o;
      }
      z = z + l7z;
      sx = sx+y+y;
      rq6t = rq6t+y+y;
      rq6t = rq6t + o;
  }

}
