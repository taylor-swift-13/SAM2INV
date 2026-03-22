int main1(int f,int y){
  int xk, rn, zfmv, db, nmn;

  xk=16;
  rn=0;
  zfmv=1;
  db=3;
  nmn=3;

  while (zfmv<=xk) {
      db = db+2*zfmv-1;
      zfmv++;
      y += rn;
  }

  while (1) {
      if (!(rn<nmn)) {
          break;
      }
      xk = (nmn)+(-(rn));
      f = f+nmn-db;
      rn += 1;
  }

}
