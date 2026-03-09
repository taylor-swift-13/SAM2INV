int main1(int z,int t){
  int dh2, db, s3;

  dh2=(z%15)+10;
  db=0;
  s3=dh2;

  while (1) {
      if (!(db<dh2)) {
          break;
      }
      db = db + 1;
      s3 = dh2-db;
      z += db;
  }

}
