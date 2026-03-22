int main1(int o){
  int jp, z, j262, ys, a3, slcn;

  jp=157;
  z=0;
  j262=0;
  ys=(o%28)+10;
  a3=0;
  slcn=o+2;

  while (1) {
      if (!(ys>j262)) {
          break;
      }
      ys -= j262;
      slcn = (1)+(slcn);
      a3 = a3*4;
      o = o+(ys%3);
      j262 += 1;
  }

  while (slcn>0) {
      jp = jp+o*o;
      z = z+o*o;
      slcn--;
      j262 = j262+o*o;
      o = o+(j262%9);
  }

}
