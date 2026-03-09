int main1(int z,int t){
  int dh2, db, s3;
  dh2=(z%15)+10;
  db=0;
  s3=dh2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s3 == dh2 - db;
  loop invariant dh2 == ((\at(z,Pre) % 15) + 10);
  loop invariant z == (\at(z,Pre)) + (db * (db + 1) / 2);
  loop invariant 0 <= db;
  loop assigns db, s3, z;
*/
while (1) {
      if (!(db<dh2)) {
          break;
      }
      db = db + 1;
      s3 = dh2-db;
      z += db;
  }
}