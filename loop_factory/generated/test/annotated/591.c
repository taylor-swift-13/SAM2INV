int main1(int w,int r){
  int db, zvv, a7n, x;
  db=w*4;
  zvv=0;
  a7n=6;
  x=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant zvv >= 0;
  loop invariant x >= 1;
  loop invariant (zvv == 0) ==> (a7n == 6);
  loop invariant db == 4 * w;
  loop invariant (zvv % 2 == 0);
  loop invariant a7n >= 1;
  loop invariant a7n <= 6;
  loop invariant (db > 0) ==> (zvv <= db);
  loop assigns zvv, a7n, x;
*/
while (1) {
      if (!(zvv<db)) {
          break;
      }
      zvv += 2;
      if (x<=a7n) {
          a7n = x;
      }
      x += a7n;
  }
}