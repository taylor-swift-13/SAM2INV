int main1(){
  int nx, pn1, e8bx;

  nx=(1%20)+5;
  pn1=(1%20)+5;
  e8bx=(1%20)+5;

  while (nx>0) {
      if (pn1>0) {
          if (e8bx>0) {
              nx = nx - 1;
              pn1 -= 1;
              e8bx--;
          }
      }
      pn1++;
  }

}
