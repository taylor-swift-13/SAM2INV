int main1(){
  int ag, na, h5gr, v, de, o4, jo3, lv, p, jas;

  ag=1+22;
  na=ag;
  h5gr=0;
  v=0;
  de=0;
  o4=0;
  jo3=0;
  lv=0;
  p=0;
  jas=na;

  while (1) {
      if (!(h5gr<=ag-1)) {
          break;
      }
      if (h5gr%10==0) {
          v++;
      }
      else {
          if (h5gr%7==0) {
              de = de + 1;
          }
          else {
              if (h5gr%3==0) {
                  o4++;
              }
              else {
                  if (1) {
                      jo3++;
                  }
              }
          }
      }
      h5gr += 1;
      p = p+h5gr%3;
      lv = (lv+o4)%5;
      jas = (jas+h5gr)%3;
  }

}
