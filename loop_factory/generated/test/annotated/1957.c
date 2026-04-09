int main1(int g){
  int ny, uq, h, m;
  ny=g;
  uq=0;
  h=ny;
  m=-8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ny == \at(g, Pre);
  loop invariant h == ny + uq*m;
  loop invariant g == \at(g, Pre) + (uq * (uq + 1)) / 2;
  loop invariant m == -8;
  loop invariant 0 <= uq && ((ny >= 0) ==> uq <= ny);
  loop assigns g, h, uq;
*/
while (1) {
      if (!(uq < ny)) {
          break;
      }
      uq += 1;
      h = h + m;
      g += uq;
  }
}