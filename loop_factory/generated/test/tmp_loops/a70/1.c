int main1(){
  int kps, v74, z, zg5, bq, b4, wqff, cjt;

  kps=(1%25)+11;
  v74=kps;
  z=9;
  zg5=0;
  bq=1;
  b4=0;
  wqff=kps;
  cjt=6;

  while (z>0&&v74<kps) {
      b4 = bq;
      if (z>=bq) {
          z = z - bq;
          zg5 = zg5 + bq;
      }
      else {
          zg5 += z;
          z = 0;
      }
      v74 = v74 + 1;
      bq++;
      if (cjt+2<kps) {
          cjt = cjt + 1;
      }
      wqff += z;
      cjt = cjt + cjt;
  }

}
