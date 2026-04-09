int main1(){
  int j2, sc, qs, xk, ucy;

  j2=1+5;
  sc=0;
  qs=j2;
  xk=j2;
  ucy=qs;

  while (1) {
      if (!(sc < j2)) {
          break;
      }
      ucy = (sc++, (ucy < qs ? ucy : qs));
      xk += j2;
      sc = j2;
  }

}
