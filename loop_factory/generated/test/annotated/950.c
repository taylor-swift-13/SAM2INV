int main1(){
  int lao, qp7x, aaqo, cy;
  lao=38;
  qp7x=3;
  aaqo=qp7x;
  cy=lao;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant aaqo <= lao;
  loop invariant cy >= lao;
  loop invariant qp7x <= lao - 1;
  loop invariant 2*(cy - lao) == (qp7x - 3) * (qp7x + 12);
  loop invariant aaqo % 5 == 3;
  loop invariant 2*cy == qp7x*qp7x + 9*qp7x + 40;
  loop invariant qp7x >= 3;
  loop invariant (aaqo == lao) || (aaqo == 3 + 5*(qp7x - 3));
  loop assigns aaqo, cy, qp7x;
*/
while (1) {
      if (aaqo+5<=lao) {
          aaqo = aaqo + 5;
      }
      else {
          aaqo = lao;
      }
      cy += qp7x;
      cy = cy + 5;
      qp7x++;
      if (qp7x>=lao) {
          break;
      }
  }
}