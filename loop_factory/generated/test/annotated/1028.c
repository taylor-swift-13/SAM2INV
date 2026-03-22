int main1(int f,int y){
  int xk, rn, zfmv, db, nmn;
  xk=16;
  rn=0;
  zfmv=1;
  db=3;
  nmn=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant db == 3 + (zfmv - 1) * (zfmv - 1);
  loop invariant zfmv >= 1;
  loop invariant zfmv <= xk + 1;
  loop invariant f == \at(f, Pre);
  loop invariant xk == 16;
  loop invariant rn == 0;
  loop invariant y == \at(y, Pre);
  loop assigns db, zfmv, y;
*/
while (zfmv<=xk) {
      db = db+2*zfmv-1;
      zfmv++;
      y += rn;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= rn <= nmn;
  loop invariant f == \at(f, Pre) + rn * (nmn - db);
  loop invariant y == \at(y, Pre);
  loop invariant nmn == 3;
  loop assigns f, rn, xk;
*/
while (1) {
      if (!(rn<nmn)) {
          break;
      }
      xk = (nmn)+(-(rn));
      f = f+nmn-db;
      rn += 1;
  }
}