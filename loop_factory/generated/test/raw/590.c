int main1(){
  int dt, vgb, r2, smxf;

  dt=1;
  vgb=0;
  r2=dt;
  smxf=dt;

  while (vgb<dt) {
      if (!(!(vgb>=dt/2))) {
          r2 += 2;
      }
      vgb++;
      smxf += r2;
  }

}
