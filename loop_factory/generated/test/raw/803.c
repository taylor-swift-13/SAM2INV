int main1(int k,int q){
  int dndb, hh, l3bx, yv;

  dndb=(k%31)+9;
  hh=0;
  l3bx=dndb;
  yv=-4;

  while (1) {
      l3bx = l3bx*3+4;
      yv = yv*l3bx+4;
      hh++;
      if (hh>=dndb) {
          break;
      }
  }

}
