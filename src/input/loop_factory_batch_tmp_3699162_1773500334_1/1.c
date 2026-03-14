int main1(int a,int j){
  int qak, k35, dk, pxh, g, b;

  qak=(a%32)+17;
  k35=qak;
  dk=0;
  pxh=0;
  g=a;
  b=a;

  while (pxh<qak) {
      pxh = pxh + 1;
      dk = dk + a;
      a = a + dk;
  }

  while (1) {
      if (!(k35<=b-1)) {
          break;
      }
      dk = k35+1;
      k35 += 2;
      g = g+b-qak;
  }

}
