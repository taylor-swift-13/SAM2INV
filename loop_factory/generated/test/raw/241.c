int main1(int h){
  int co, u, bz9, li, vz, t5l;

  co=54;
  u=0;
  bz9=0;
  li=h+6;
  vz=0;
  t5l=u;

  while (bz9+1<=co) {
      if (vz<co) {
          li = bz9;
      }
      bz9++;
      t5l = t5l + bz9;
  }

  while (vz>0) {
      li = li+t5l*vz;
      u = u + li;
      vz = 0;
  }

}
