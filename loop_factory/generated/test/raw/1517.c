int main1(int z){
  int tz1l, d, rv, xz, ahl, ls, l7, xv, jv7b;

  tz1l=z*3;
  d=0;
  rv=0;
  xz=12;
  ahl=-2;
  ls=z*3;
  l7=0;
  xv=tz1l;
  jv7b=tz1l;

  while (d+3<=tz1l) {
      if (d<tz1l/2) {
          rv += xz;
      }
      else {
          rv++;
      }
      if (ls<ahl+3) {
          l7 += d;
      }
      ahl += 2;
      jv7b = jv7b+(d%2);
      xv += rv;
      xz += 4;
      ahl += xz;
      tz1l = (d+3)-1;
      if (!(!((d%2)==0))) {
          ls += z;
      }
      else {
          ls += z;
      }
  }

}
