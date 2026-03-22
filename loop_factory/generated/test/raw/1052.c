int main1(){
  int i6, lhk, r9, bb, i94, x6;

  i6=67;
  lhk=-3;
  r9=0;
  bb=0;
  i94=0;
  x6=-5;

  while (bb<i6) {
      r9 = r9 + 1;
      x6 = x6 + lhk;
      i94++;
      bb++;
  }

  while (i6<=x6-1) {
      i6 = i6 + 1;
      bb++;
      i94 = i94+(bb%8);
  }

}
