int main1(){
  int hor, r08, ub, xz, e1z, v1v;

  hor=63;
  r08=hor;
  ub=0;
  xz=0;
  e1z=4;
  v1v=r08;

  while (1) {
      if (!(ub<hor&&e1z>0)) {
          break;
      }
      ub += 1;
      xz += e1z;
      e1z = e1z - 1;
      v1v += xz;
  }

}
