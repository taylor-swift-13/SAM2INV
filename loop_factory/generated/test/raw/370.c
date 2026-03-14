int main1(){
  int qc, wxhm, l, i4;

  qc=-2;
  wxhm=0;
  l=(1%28)+10;
  i4=20;

  while (l>wxhm) {
      l -= wxhm;
      i4 += qc;
      wxhm += 1;
      i4 = (i4)+(i4*i4);
  }

  while (1) {
      if (!(wxhm<=qc-1)) {
          break;
      }
      wxhm += 1;
  }

}
