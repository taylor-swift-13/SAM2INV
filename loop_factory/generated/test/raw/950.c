int main1(){
  int lao, qp7x, aaqo, cy;

  lao=38;
  qp7x=3;
  aaqo=qp7x;
  cy=lao;

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
