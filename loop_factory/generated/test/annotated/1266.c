int main1(int t,int w){
  int fbb, mtf8, ma, q, j3h;
  fbb=168;
  mtf8=fbb;
  ma=3;
  q=-1;
  j3h=w;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant fbb == 168;
  loop invariant ma % 3 == 0;
  loop invariant (q == -1) || (q == 0);
  loop invariant (mtf8 == 168) || (mtf8 == 2);
  loop invariant t == \at(t, Pre);
  loop invariant w == \at(w, Pre);
  loop invariant (j3h - w) % 3 == 0;
  loop invariant ma >= 3;
  loop invariant j3h >= w;
  loop invariant (fbb == 168) &&
                 ((ma == 3 && q == -1 && j3h == w && mtf8 == 168) ||
                  (ma == 6 && q == 0 && j3h == w + 3 && mtf8 == 2));
  loop invariant (mtf8 == 168 || mtf8 == 2) &&
                 ((ma == 3) || (ma == 6)) &&
                 ((q == -1) || (q == 0)) &&
                 (((j3h - w) == 0) || ((j3h - w) == 3));
  loop assigns ma, q, j3h, mtf8;
*/
while (1) {
      if (!(mtf8>=3)) {
          break;
      }
      ma = ma*2;
      q = q/2;
      j3h = j3h + 3;
      mtf8 = 2;
  }
}