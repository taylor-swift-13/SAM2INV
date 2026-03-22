int main1(int y){
  int e7x, qz7p, mrb, r, t4, f7z5, t6sw, jyf, h5gq;

  e7x=y;
  qz7p=0;
  mrb=0;
  r=0;
  t4=0;
  f7z5=y;
  t6sw=20;
  jyf=e7x;
  h5gq=e7x;

  while (qz7p<e7x) {
      r = r + 1;
      t4 = t4 + 1;
      if (r>=12) {
          r = r - 12;
          mrb = mrb + 1;
      }
      qz7p = qz7p + 1;
      if (qz7p<y+3) {
          f7z5 += qz7p;
      }
      jyf += qz7p;
      y += 2;
      t6sw += 2;
      h5gq += 2;
      f7z5 += t6sw;
  }

}
